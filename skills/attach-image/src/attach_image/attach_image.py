"""Load on-disk images into the model's context as multimodal attachments."""

from __future__ import annotations

import base64
import io
from pathlib import Path

# Keep in sync with ATTACHMENT_DISPLAY_MIME in src/core/kernel/index.ts.
_ATTACHMENT_DISPLAY_MIME = "application/vnd.eukhe.attachment+json"

_MAX_SOURCE_IMAGE_BYTES = 20_000_000
_MAX_SOURCE_IMAGE_PIXELS = 36_000_000
# Anthropic's recommended long side (Claude scales larger images down to it)
# and the attachment size omp keeps images under; a model's own
# inputLimits.images.resize lowers them.
_MAX_ATTACHMENT_DIMENSION = 1568
_MAX_ATTACHMENT_BYTES = 500 * 1024
_TRANSPARENCY_BACKGROUND = "#888888"
_JPEG_QUALITY = 80
_JPEG_QUALITY_LADDER = (70, 60, 50, 40)
_SCALES = (1.0, 0.75, 0.5, 0.35, 0.25)

# Matches IMAGE_MIME_TYPES in src/utils/mime.ts.
_IMAGE_SIGNATURES = (
    ("image/png", b"\x89PNG\r\n\x1a\n"),
    ("image/jpeg", b"\xff\xd8\xff"),
    ("image/gif", b"GIF87a"),
    ("image/gif", b"GIF89a"),
)


def _detect_image_mime(data: bytes) -> str | None:
    for mime, prefix in _IMAGE_SIGNATURES:
        if data.startswith(prefix):
            return mime
    if data[:4] == b"RIFF" and data[8:12] == b"WEBP":
        return "image/webp"
    return None


def _image_dimensions(filepath: Path) -> tuple[int, int]:
    try:
        from PIL import Image
    except ImportError as error:
        raise RuntimeError(
            "attach_image needs Pillow to inspect this image before loading it into context."
        ) from error

    try:
        with Image.open(filepath) as image:
            return image.size
    except Exception as error:
        raise ValueError(
            f"{filepath} is not a readable supported image (PNG, JPEG, GIF, WebP)."
        ) from error


def _validate_decodable_image(filepath: Path) -> None:
    try:
        from PIL import Image

        with Image.open(filepath) as image:
            if getattr(image, "is_animated", False):
                image.seek(0)
            image.load()
    except Exception as error:
        raise ValueError(
            f"{filepath} is not a readable supported image (PNG, JPEG, GIF, WebP)."
        ) from error


def _validate_image(path: str) -> tuple[Path, str, int, tuple[int, int]]:
    filepath = Path(path).expanduser()
    if not filepath.is_file():
        raise FileNotFoundError(f"{path} is not an existing regular file")

    size = filepath.stat().st_size
    if size > _MAX_SOURCE_IMAGE_BYTES:
        raise ValueError(
            f"{path} is {size // 1_000_000}MB; images must be under "
            f"{_MAX_SOURCE_IMAGE_BYTES // 1_000_000}MB. Resize it first."
        )

    with filepath.open("rb") as f:
        head = f.read(16)
    mime = _detect_image_mime(head)
    if mime is None:
        raise ValueError(
            f"{path} is not a supported image (PNG, JPEG, GIF, WebP). "
            "Only images can be loaded into context; open other files in the kernel instead."
        )

    dimensions = _image_dimensions(filepath)
    pixel_count = dimensions[0] * dimensions[1]
    if pixel_count > _MAX_SOURCE_IMAGE_PIXELS:
        raise ValueError(
            f"{path} is {dimensions[0]}x{dimensions[1]} ({pixel_count // 1_000_000}MP); "
            f"images must be at most {_MAX_SOURCE_IMAGE_PIXELS // 1_000_000}MP. Resize it first."
        )
    _validate_decodable_image(filepath)

    return filepath, mime, size, dimensions


class _Limits:
    """The attachment limits for the current model: the defaults above,
    lowered by the model's `inputLimits.images` (`resize.maxWidth`,
    `resize.maxHeight`, `resize.maxBytes` on the base64 payload,
    `resize.jpegQuality`, `maxPerMessage`)."""

    def __init__(self, info: dict) -> None:
        images = (info.get("inputLimits") or {}).get("images") or {}
        resize = images.get("resize") or {}
        self.max_width = min(_MAX_ATTACHMENT_DIMENSION, resize.get("maxWidth") or _MAX_ATTACHMENT_DIMENSION)
        self.max_height = min(_MAX_ATTACHMENT_DIMENSION, resize.get("maxHeight") or _MAX_ATTACHMENT_DIMENSION)
        payload = resize.get("maxBytes")
        self.max_bytes = min(_MAX_ATTACHMENT_BYTES, payload // 4 * 3) if payload else _MAX_ATTACHMENT_BYTES
        first = min(_JPEG_QUALITY, resize.get("jpegQuality") or _JPEG_QUALITY)
        self.jpeg_qualities = (first, *(quality for quality in _JPEG_QUALITY_LADDER if quality < first))
        self.max_per_message = images.get("maxPerMessage")


def _load_image_for_attachment(data: bytes):
    """The first frame, EXIF-rotated, in RGB or (with transparency) RGBA, and
    whether it was animated."""
    from PIL import Image, ImageOps

    image = Image.open(io.BytesIO(data))
    is_animated = getattr(image, "is_animated", False)
    if is_animated:
        image.seek(0)
    image = ImageOps.exif_transpose(image)
    is_transparent = image.mode in {"RGBA", "LA"} or (image.mode == "P" and "transparency" in image.info)
    return image.convert("RGBA" if is_transparent else "RGB"), is_animated


def _encode(image, format: str, quality: int | None = None) -> bytes:
    buffer = io.BytesIO()
    if format == "PNG":
        image.save(buffer, format="PNG", optimize=True)
    else:
        image.save(buffer, format="JPEG", quality=quality, optimize=True, progressive=True)
    return buffer.getvalue()


def _resize_image(
    filepath: Path, mime_type: str, size: int, dimensions: tuple[int, int], limits: _Limits
) -> tuple[str, str, str | None]:
    """The image as attached: the file as it is when within `limits`, else
    resized to fit them, as PNG when that fits the byte limit (lossless, for
    thin lines and text) and as JPEG otherwise, scaling down further only
    when no JPEG quality fits."""
    data = filepath.read_bytes()
    width, height = dimensions
    if width <= limits.max_width and height <= limits.max_height and size <= limits.max_bytes:
        return base64.b64encode(data).decode("ascii"), mime_type, None

    try:
        from PIL import Image
    except ImportError as error:
        raise RuntimeError(
            "attach_image needs Pillow to resize this image before loading it into context."
        ) from error

    image, is_animated = _load_image_for_attachment(data)
    original_width, original_height = image.size
    fit = min(1.0, limits.max_width / original_width, limits.max_height / original_height)
    smallest: tuple[int, int, int] | None = None
    for scale in _SCALES:
        target_width = round(original_width * fit * scale)
        target_height = round(original_height * fit * scale)
        if target_width < 1 or target_height < 1:
            break
        resized = image.resize((target_width, target_height), Image.Resampling.LANCZOS)
        candidates = [("PNG", None)] + [("JPEG", quality) for quality in limits.jpeg_qualities]
        for format, quality in candidates:
            notes = ["animated image flattened to first frame"] if is_animated else []
            source = resized
            if format == "JPEG" and resized.mode == "RGBA":
                source = Image.new("RGB", resized.size, _TRANSPARENCY_BACKGROUND)
                source.paste(resized, mask=resized.split()[-1])
                notes.append(f"transparent pixels composited on {_TRANSPARENCY_BACKGROUND} background")
            candidate = _encode(source, format, quality)
            if smallest is None or len(candidate) < smallest[0]:
                smallest = (len(candidate), target_width, target_height)
            if len(candidate) <= limits.max_bytes:
                encoding = "PNG" if quality is None else f"JPEG at quality {quality}"
                note = "; ".join(
                    [f"original {original_width}x{original_height}; attached {target_width}x{target_height} {encoding}"]
                    + notes
                )
                return base64.b64encode(candidate).decode("ascii"), f"image/{format.lower()}", note

    smallest_bytes, smallest_width, smallest_height = smallest or (0, 0, 0)
    raise ValueError(
        f"{filepath} could not be compressed below {limits.max_bytes // 1024}KB "
        f"(smallest was {smallest_bytes // 1024}KB at {smallest_width}x{smallest_height})."
    )


def _emit_attachment(
    filepath: Path, mime_type: str, size: int, dimensions: tuple[int, int], limits: _Limits
) -> str | None:
    from rlm import emit

    data_b64, emitted_mime_type, resize_note = _resize_image(filepath, mime_type, size, dimensions, limits)
    emit(
        {
            _ATTACHMENT_DISPLAY_MIME: {"mime_type": emitted_mime_type, "data": data_b64, "path": str(filepath)},
            "text/plain": f"Loaded image into context: {filepath}",
        }
    )
    return resize_note


async def run(*paths: str) -> str:
    """Load one or more on-disk images into the model's context as attachments.

    Use this when the model needs to actually SEE an image file — a screenshot,
    diagram, chart, photo, or scanned page. The image is sent to the model as a
    viewable attachment (the same way a pasted image is).

    Do NOT use this for programmatic image analysis (reading pixels, cropping,
    resizing, hashing, measuring colors). For that, open the file with PIL in
    the kernel instead.

    Args:
        *paths: One or more image paths. Relative, absolute, or `~`-prefixed.
            Supported formats: PNG, JPEG, GIF, WebP. Other types (PDF, audio,
            video) are not supported and raise an error.

    Returns:
        A short confirmation listing the images loaded into context.

    Raises:
        FileNotFoundError: If a path does not exist or is not a regular file.
        ValueError: If a file is not a supported image, is too large, or cannot
            be compressed enough for safe inline rendering and replay.
        RuntimeError: If the current model cannot accept images.
    """
    if not paths:
        raise ValueError("attach_image requires at least one image path")

    from rlm import host_request

    info = await host_request("model.info")
    if "image" not in info.get("input", []):
        model_id = info.get("id") or "the current model"
        raise RuntimeError(
            f"{model_id} does not support vision. "
            "Tell the user to switch to a vision-capable model to load images into context."
        )

    limits = _Limits(info)
    if limits.max_per_message is not None and len(paths) > limits.max_per_message:
        raise ValueError(
            f"{info.get('id') or 'this model'} takes at most {limits.max_per_message} images "
            "per message; attach them in smaller groups."
        )

    # Validate every path before emitting anything, so a later failure never
    # leaves a partial subset injected.
    validated = [_validate_image(path) for path in paths]
    resize_notes = []
    for filepath, mime, size, dimensions in validated:
        note = _emit_attachment(filepath, mime, size, dimensions, limits)
        if note:
            resize_notes.append(f"{filepath}: {note}")

    message = f"Loaded {len(validated)} image(s) into context: {', '.join(paths)}"
    if resize_notes:
        message += "\nResized for efficient inline rendering/replay:\n- " + "\n- ".join(resize_notes)
    return message
