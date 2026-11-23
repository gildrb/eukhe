from __future__ import annotations

import asyncio
import base64
import importlib.util
import io
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import AsyncMock, MagicMock, patch

from PIL import Image


SKILL = Path(__file__).parents[2] / "skills/attach-image/src/attach_image/attach_image.py"
VISION = {"id": "m", "provider": "p", "input": ["text", "image"], "inputLimits": None}


def _load():
    spec = importlib.util.spec_from_file_location("attach_image_skill", SKILL)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _attach(path: Path, info: dict = VISION) -> tuple[list[tuple[str, int, int]], str]:
    """Attach `path` for a model described by `info`: the (mime type, width,
    height) of each emitted image, and the returned message."""
    emit = MagicMock()
    with patch("rlm.host_request", AsyncMock(return_value=info)), patch("rlm.emit", emit):
        message = asyncio.run(_load().run(str(path)))
    attached = []
    for call in emit.call_args_list:
        payload = call.args[0]["application/vnd.eukhe.attachment+json"]
        with Image.open(io.BytesIO(base64.b64decode(payload["data"]))) as image:
            attached.append((payload["mime_type"], *image.size))
    return attached, message


class AttachImageSkillTest(unittest.TestCase):
    def setUp(self) -> None:
        self.dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.dir.cleanup)

    def _save(self, name: str, image: Image.Image) -> Path:
        path = Path(self.dir.name) / name
        image.save(path)
        return path

    def test_a_large_screenshot_keeps_png_at_the_1568_pixel_long_side(self) -> None:
        # Flat UI colors: the resized PNG fits the byte limit, so thin lines
        # stay lossless.
        image = Image.new("RGB", (2880, 1800), "white")
        image.paste((30, 30, 30), (0, 0, 2880, 1))
        path = self._save("shot.png", image)
        attached, message = _attach(path)
        self.assertEqual(attached, [("image/png", 1568, 980)])
        self.assertIn("original 2880x1800; attached 1568x980 PNG", message)

    def test_a_photo_too_large_as_png_becomes_jpeg(self) -> None:
        noise = Image.frombytes("RGB", (2000, 1500), os.urandom(2000 * 1500 * 3))
        path = self._save("photo.png", noise)
        [(mime, width, _)], _ = _attach(path)
        self.assertEqual(mime, "image/jpeg")
        self.assertLessEqual(width, 1568)

    def test_an_image_within_the_limits_is_attached_as_it_is(self) -> None:
        path = self._save("small.png", Image.new("RGB", (1440, 900), "white"))
        emit = MagicMock()
        with patch("rlm.host_request", AsyncMock(return_value=VISION)), patch("rlm.emit", emit):
            asyncio.run(_load().run(str(path)))
        payload = emit.call_args.args[0]["application/vnd.eukhe.attachment+json"]
        self.assertEqual(
            (payload["mime_type"], base64.b64decode(payload["data"])),
            ("image/png", path.read_bytes()),
        )

    def test_the_models_image_limits_lower_the_size(self) -> None:
        path = self._save("shot.png", Image.new("RGB", (1440, 900), "white"))
        info = {
            **VISION,
            "inputLimits": {"images": {"resize": {"maxWidth": 1000, "maxHeight": 1000}}},
        }
        attached, _ = _attach(path, info)
        self.assertEqual(attached, [("image/png", 1000, 625)])

    def test_more_paths_than_the_model_takes_per_message_attach_nothing(self) -> None:
        path = self._save("a.png", Image.new("RGB", (10, 10), "white"))
        info = {**VISION, "inputLimits": {"images": {"maxPerMessage": 1}}}
        emit = MagicMock()
        with patch("rlm.host_request", AsyncMock(return_value=info)), patch("rlm.emit", emit):
            with self.assertRaisesRegex(ValueError, "at most 1 images per message"):
                asyncio.run(_load().run(str(path), str(path)))
        emit.assert_not_called()


if __name__ == "__main__":
    unittest.main()
