#lang forge

option problem_type temporal
option max_tracelength 14

abstract sig Color {}
one sig White, Green, Orange, Red, Blue, Yellow extends Color {}

abstract sig Position {}
one sig TL, TM, TR, ML, MR, BL, BM, BR extends Position {}

abstract sig Face {
	center: one Color,
	var stickers: set Position->Color,
	toup: one Face,
	todown: one Face,
	toleft: one Face,
	toright: one Face
}

one sig UFace, FFace, LFace, RFace, BFace, DFace extends Face {}

pred orientations {
	-- Toup, todown, etc	
	UFace.toup = BFace
	UFace.toright = RFace
	UFace.toleft = LFace
	UFace.todown = FFace

	FFace.toup = UFace
	FFace.toright = RFace
	FFace.toleft = LFace
	FFace.todown = DFace

	LFace.toup = UFace
	LFace.toright = FFace
	LFace.toleft = BFace
	LFace.todown = DFace

	RFace.toup = UFace
	RFace.toright = BFace
	RFace.toleft = FFace
	RFace.todown = DFace

	BFace.toup = UFace
	BFace.toright = LFace
	BFace.toleft = RFace
	BFace.todown = DFace

	DFace.toup = FFace
	DFace.toright = RFace
	DFace.toleft = LFace
	DFace.todown = BFace
}

pred basics {
	orientations

	-- ADD HARD-CODING OF FACE FIELDS HERE (TOUP, TODOWN, ETC.)
	UFace.center = White
	FFace.center = Green
	LFace.center = Orange
	RFace.center = Red
	BFace.center = Blue
	DFace.center = Yellow

	-- enforces that each sticker is set to exactly one color
	all face: Face | {
		all pos: Position | {
			one face.stickers[pos]
		}
	}
}

test expect {
	eightStickersPerFace : {basics implies (all f : Face | #(f.stickers) = 8)} is theorem
}

pred solved {
	all face: Face | {
		face.stickers[Position] = face.center
	}
}

run { basics solved }