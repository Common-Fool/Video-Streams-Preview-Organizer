"""Рисует иконку VO SP: лист превью (сетка кадров) с кнопкой воспроизведения. Нужен Pillow (только для разработки).

    python assets/make_icon.py   ->  assets/vo_sp.ico, assets/vo_sp.png
"""
import os

from PIL import Image, ImageDraw

HERE = os.path.dirname(os.path.abspath(__file__))
TOP, BOTTOM = (124, 92, 255), (30, 170, 255)   # фон: фиолетовый → голубой
SS = 4                                           # сглаживание: рисуем крупнее и уменьшаем


def gradient(n):
    g = Image.new('RGB', (1, n))
    for y in range(n):
        k = y / max(1, n - 1)
        g.putpixel((0, y), tuple(round(a + (b - a) * k) for a, b in zip(TOP, BOTTOM)))
    return g.resize((n, n))


def draw(size):
    n = size * SS
    img = Image.new('RGBA', (n, n), (0, 0, 0, 0))
    mask = Image.new('L', (n, n), 0)
    pad = round(n * 0.04)
    ImageDraw.Draw(mask).rounded_rectangle([pad, pad, n - pad, n - pad], radius=round(n * 0.22), fill=255)
    img.paste(gradient(n), (0, 0), mask)
    over = Image.new('RGBA', (n, n), (0, 0, 0, 0))
    d = ImageDraw.Draw(over)
    if size >= 40:  # сетка кадров 3×3 — на мелких размерах она превращается в шум
        m, gap = n * 0.2, n * 0.045
        cell = (n - 2 * m - 2 * gap) / 3
        for r in range(3):
            for c in range(3):
                x, y = m + c * (cell + gap), m + r * (cell + gap)
                d.rounded_rectangle([x, y, x + cell, y + cell], radius=cell * 0.18, fill=(255, 255, 255, 85))
    # кнопка воспроизведения в центре
    cx = cy = n / 2
    rad = n * (0.21 if size >= 40 else 0.32)
    d.ellipse([cx - rad, cy - rad, cx + rad, cy + rad], fill=(255, 255, 255, 255))
    t = rad * 0.52
    d.polygon([(cx - t * 0.62, cy - t), (cx - t * 0.62, cy + t), (cx + t * 1.0, cy)], fill=(84, 118, 255, 255))
    img = Image.alpha_composite(img, over)
    return img.resize((size, size), Image.LANCZOS)


if __name__ == '__main__':
    sizes = [16, 20, 24, 32, 40, 48, 64, 128, 256]
    imgs = [draw(s) for s in sizes]
    imgs[-1].save(os.path.join(HERE, 'vo_sp.ico'), sizes=[(s, s) for s in sizes], append_images=imgs[:-1])
    draw(512).save(os.path.join(HERE, 'vo_sp.png'))
