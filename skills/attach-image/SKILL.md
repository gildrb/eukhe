---
name: attach-image
description: Put an image file (PNG, JPEG, GIF, WebP) into your context so you can see it - screenshots, diagrams, charts, photos, scanned pages. Use when you must look at an image's content; for pixel math, cropping or hashing, open the file with Pillow in the REPL instead. Needs a vision-capable model.
---

# Attach Image

`print(await attach_image("a.png", "b.jpg"))` attaches each file like a pasted image.

- See vs compute: attach only to look. To measure, crop, resize or compare, use `PIL.Image.open(path)` in the REPL; that keeps the image out of context.
- Large images are resized and compressed for context; the file on disk is unchanged. An animated image that needs compression keeps its first frame; transparency becomes a gray background. A huge image (pixel count) is refused.
- An unsupported file or a model without vision raises an error with the reason; do not retry it.
