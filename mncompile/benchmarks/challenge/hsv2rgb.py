import colorsys


def kernel(hsv):
    return [list(colorsys.hsv_to_rgb(*color)) for color in hsv]
