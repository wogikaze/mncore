import colorsys


def kernel(x):
    return [colorsys.hsv_to_rgb(*color) for color in x]
