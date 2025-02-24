#!/usr/bin/python3

# Program generating the logo

from PIL import Image, ImageDraw
from math import pi, sin, cos
from pathlib import Path

# Parameters found by trial and error
WIDTH = 480
HEIGHT_FRACTAL = 300
HEIGHT_BASIS = 20
WIDTH_BASIS = 100
HEIGHT_TREE = WIDTH - HEIGHT_BASIS

# Constants for the fractal

INITIAL_LENGTH = 50
INITIAL_WIDTH = 8
COEFF = 0.9
ANGLE_BRANCH_DEVIATION = pi/10

# Number of steps of drawings i nthe (kind of) fractal

NBR_STEPS = 9

IMAGE_LOCATION_WITHOUT_EXTENSION = str(
	Path(__file__).parent.resolve()
) + "/../Images/Logo.png"

color = "#B2F613"
	
logo = Image.new('RGBA', (WIDTH, WIDTH), (0,0,0,0))

def drawFractal(logo, nbrSteps, coordsRoot, angleWithVertical):
	if nbrSteps > 0:
		newRoot = (
			coordsRoot[0] + INITIAL_LENGTH *
					(COEFF**(NBR_STEPS - nbrSteps + 1)) *
					sin(angleWithVertical),
			coordsRoot[1] - INITIAL_LENGTH *
					(COEFF**(NBR_STEPS - nbrSteps + 1)) *
					cos(angleWithVertical)
		)

		shape = [coordsRoot, newRoot]

		ImageDraw.Draw(logo).line(
			shape,
			fill = color,
			width = int(
				INITIAL_WIDTH * (COEFF**(NBR_STEPS - nbrSteps + 1))
			)
		)

		drawFractal(
			logo, 
			nbrSteps - 1, 
			newRoot, 
			angleWithVertical + ANGLE_BRANCH_DEVIATION
		)

		drawFractal(
			logo, 
			nbrSteps - 1, 
			newRoot, 
			angleWithVertical - ANGLE_BRANCH_DEVIATION
		)

drawFractal(logo, NBR_STEPS, (WIDTH/2, HEIGHT_FRACTAL), 0)

# We make the trunk longer in order to make the image square
# and make it look more like a tree
shape = [(WIDTH/2, HEIGHT_FRACTAL), (WIDTH/2, HEIGHT_TREE)]
ImageDraw.Draw(logo).line(shape, fill = color, width = int(INITIAL_WIDTH))

# The basis of the tree
shape = [
	(WIDTH/2 + INITIAL_WIDTH/2, HEIGHT_TREE),
	(WIDTH/2 + WIDTH_BASIS/2, WIDTH),
	(WIDTH/2 - WIDTH_BASIS/2, WIDTH),
	(WIDTH/2 - INITIAL_WIDTH/2, HEIGHT_TREE)
]

ImageDraw.Draw(logo).polygon(shape, fill = color)

logo.save(IMAGE_LOCATION_WITHOUT_EXTENSION)
