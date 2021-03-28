#lang forge

abstract sig Color {}
one sig White, Green, Orange, Red, Blue, Yellow extends Color {}

abstract sig Position {}
one TL, TM, TR, ML, MR, BL, BM, BR extends Position {}

abstract sig Face {
	center: one Color
	stickers: set Position->Color
	toup: one Face
	todown: one Face
	toleft: one Face
	toright: one Face
}

one UFace, FFace, LFace, RFace, BFace, DFace extends Face {}

pred basics {
	all face: Face | {
		all pos: Position | {
			one face.stickers.pos
		}
	}
}

pred solved {

}