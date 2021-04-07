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
	toright: one Face,
	rot: set (Face->Position)->(Face->Position)
}

-- stickers: Face->Position->Color
-- stickers[Face->Position] --> gives us the color

pred rotate[rf: Face] {
    all f: Face | {
        all p: Position | {
            stickers[f->p] = stickers'[rf.rot[f->p]]
        }
    }
}

pred rotations {
    --- UFace Rotations
    UFace.rot =
    (UFace->TL)->(UFace->TR) + -- Current Face
    (UFace->TM)->(UFace->MR) + -- Current Face
    (UFace->TR)->(UFace->BR) + -- Current Face
    (UFace->ML)->(UFace->TM) + -- Current Face
    (UFace->MR)->(UFace->BM) + -- Current Face
    (UFace->BL)->(UFace->TL) + -- Current Face
    (UFace->BM)->(UFace->ML) + -- Current Face
    (UFace->BR)->(UFace->BL) + -- Current Face
    (FFace->TL)->(LFace->TL) + --
    (FFace->TM)->(LFace->TM) + --
    (FFace->TR)->(LFace->TR) + --
    (FFace->ML)->(FFace->ML) +
    (FFace->MR)->(FFace->MR) +
    (FFace->BL)->(FFace->BL) +
    (FFace->BM)->(FFace->BM) +
    (FFace->BR)->(FFace->BR) +
    (LFace->TL)->(BFace->TL) + --
    (LFace->TM)->(BFace->TM) + --
    (LFace->TR)->(BFace->TR) + --
    (LFace->ML)->(LFace->ML) +
    (LFace->MR)->(LFace->MR) +
    (LFace->BL)->(LFace->BL) +
    (LFace->BM)->(LFace->BM) +
    (LFace->BR)->(LFace->BR) +
    (RFace->TL)->(FFace->TL) + --
    (RFace->TM)->(FFace->TM) + --
    (RFace->TR)->(FFace->TR) + --
    (RFace->ML)->(RFace->ML) +
    (RFace->MR)->(RFace->MR) +
    (RFace->BL)->(RFace->BL) +
    (RFace->BM)->(RFace->BM) +
    (RFace->BR)->(RFace->BR) +
    (BFace->TL)->(RFace->TL) + --
    (BFace->TM)->(RFace->TM) + --
    (BFace->TR)->(RFace->TR) + --
    (BFace->ML)->(BFace->ML) +
    (BFace->MR)->(BFace->MR) +
    (BFace->BL)->(BFace->BL) +
    (BFace->BM)->(BFace->BM) +
    (BFace->BR)->(BFace->BR) +
    (DFace->TL)->(DFace->TL) + -- Opposite Face
    (DFace->TM)->(DFace->TM) + -- Opposite Face
    (DFace->TR)->(DFace->TR) + -- Opposite Face
    (DFace->ML)->(DFace->ML) + -- Opposite Face
    (DFace->MR)->(DFace->MR) + -- Opposite Face
    (DFace->BL)->(DFace->BL) + -- Opposite Face
    (DFace->BM)->(DFace->BM) + -- Opposite Face
    (DFace->BR)->(DFace->BR)   -- Opposite Face

    --- FFace Rotations
    FFace.rot =
    (UFace->TL)->(UFace->TL) +
    (UFace->TM)->(UFace->TM) +
    (UFace->TR)->(UFace->TR) +
    (UFace->ML)->(UFace->ML) +
    (UFace->MR)->(UFace->MR) +
    (UFace->BL)->(UFace->BL) +
    (UFace->BM)->(UFace->BM) +
    (UFace->BR)->(UFace->BR) +
    (FFace->TL)->(FFace->TR) + -- Current Face
    (FFace->TM)->(FFace->MR) + -- Current Face
    (FFace->TR)->(FFace->BR) + -- Current Face
    (FFace->ML)->(FFace->TM) + -- Current Face
    (FFace->MR)->(FFace->BM) + -- Current Face
    (FFace->BL)->(FFace->TL) + -- Current Face
    (FFace->BM)->(FFace->ML) + -- Current Face
    (FFace->BR)->(FFace->BL) + -- Current Face
    (LFace->TL)->(LFace->TL) +
    (LFace->TM)->(LFace->TM) +
    (LFace->TR)->(LFace->TR) +
    (LFace->ML)->(LFace->ML) +
    (LFace->MR)->(LFace->MR) +
    (LFace->BL)->(LFace->BL) +
    (LFace->BM)->(LFace->BM) +
    (LFace->BR)->(LFace->BR) +
    (RFace->TL)->(RFace->TL) +
    (RFace->TM)->(RFace->TM) +
    (RFace->TR)->(RFace->TR) +
    (RFace->ML)->(RFace->ML) +
    (RFace->MR)->(RFace->MR) +
    (RFace->BL)->(RFace->BL) +
    (RFace->BM)->(RFace->BM) +
    (RFace->BR)->(RFace->BR) +
    (BFace->TL)->(BFace->TL) + -- Opposite Face
    (BFace->TM)->(BFace->TM) + -- Opposite Face
    (BFace->TR)->(BFace->TR) + -- Opposite Face
    (BFace->ML)->(BFace->ML) + -- Opposite Face
    (BFace->MR)->(BFace->MR) + -- Opposite Face
    (BFace->BL)->(BFace->BL) + -- Opposite Face
    (BFace->BM)->(BFace->BM) + -- Opposite Face
    (BFace->BR)->(BFace->BR) + -- Opposite Face
    (DFace->TL)->(DFace->TL) +
    (DFace->TM)->(DFace->TM) +
    (DFace->TR)->(DFace->TR) +
    (DFace->ML)->(DFace->ML) +
    (DFace->MR)->(DFace->MR) +
    (DFace->BL)->(DFace->BL) +
    (DFace->BM)->(DFace->BM) +
    (DFace->BR)->(DFace->BR)

    --- LFace Rotations
    LFace.rot =
    (UFace->TL)->(UFace->TL) +
    (UFace->TM)->(UFace->TM) +
    (UFace->TR)->(UFace->TR) +
    (UFace->ML)->(UFace->ML) +
    (UFace->MR)->(UFace->MR) +
    (UFace->BL)->(UFace->BL) +
    (UFace->BM)->(UFace->BM) +
    (UFace->BR)->(UFace->BR) +
    (FFace->TL)->(FFace->TL) +
    (FFace->TM)->(FFace->TM) +
    (FFace->TR)->(FFace->TR) +
    (FFace->ML)->(FFace->ML) +
    (FFace->MR)->(FFace->MR) +
    (FFace->BL)->(FFace->BL) +
    (FFace->BM)->(FFace->BM) +
    (FFace->BR)->(FFace->BR) +
    (LFace->TL)->(LFace->TR) + -- Current Face
    (LFace->TM)->(LFace->MR) + -- Current Face
    (LFace->TR)->(LFace->BR) + -- Current Face
    (LFace->ML)->(LFace->TM) + -- Current Face
    (LFace->MR)->(LFace->BM) + -- Current Face
    (LFace->BL)->(LFace->TL) + -- Current Face
    (LFace->BM)->(LFace->ML) + -- Current Face
    (LFace->BR)->(LFace->BL) + -- Current Face
    (RFace->TL)->(RFace->TL) + -- Opposite Face
    (RFace->TM)->(RFace->TM) + -- Opposite Face
    (RFace->TR)->(RFace->TR) + -- Opposite Face
    (RFace->ML)->(RFace->ML) + -- Opposite Face
    (RFace->MR)->(RFace->MR) + -- Opposite Face
    (RFace->BL)->(RFace->BL) + -- Opposite Face
    (RFace->BM)->(RFace->BM) + -- Opposite Face
    (RFace->BR)->(RFace->BR) + -- Opposite Face
    (BFace->TL)->(BFace->TL) +
    (BFace->TM)->(BFace->TM) +
    (BFace->TR)->(BFace->TR) +
    (BFace->ML)->(BFace->ML) +
    (BFace->MR)->(BFace->MR) +
    (BFace->BL)->(BFace->BL) +
    (BFace->BM)->(BFace->BM) +
    (BFace->BR)->(BFace->BR) +
    (DFace->TL)->(DFace->TL) +
    (DFace->TM)->(DFace->TM) +
    (DFace->TR)->(DFace->TR) +
    (DFace->ML)->(DFace->ML) +
    (DFace->MR)->(DFace->MR) +
    (DFace->BL)->(DFace->BL) +
    (DFace->BM)->(DFace->BM) +
    (DFace->BR)->(DFace->BR)

    --- RFace Rotations
    RFace.rot =
    (UFace->TL)->(UFace->TL) +
    (UFace->TM)->(UFace->TM) +
    (UFace->TR)->(UFace->TR) +
    (UFace->ML)->(UFace->ML) +
    (UFace->MR)->(UFace->MR) +
    (UFace->BL)->(UFace->BL) +
    (UFace->BM)->(UFace->BM) +
    (UFace->BR)->(UFace->BR) +
    (FFace->TL)->(FFace->TL) +
    (FFace->TM)->(FFace->TM) +
    (FFace->TR)->(FFace->TR) +
    (FFace->ML)->(FFace->ML) +
    (FFace->MR)->(FFace->MR) +
    (FFace->BL)->(FFace->BL) +
    (FFace->BM)->(FFace->BM) +
    (FFace->BR)->(FFace->BR) +
    (LFace->TL)->(LFace->TL) + -- Opposite Face
    (LFace->TM)->(LFace->TM) + -- Opposite Face
    (LFace->TR)->(LFace->TR) + -- Opposite Face
    (LFace->ML)->(LFace->ML) + -- Opposite Face
    (LFace->MR)->(LFace->MR) + -- Opposite Face
    (LFace->BL)->(LFace->BL) + -- Opposite Face
    (LFace->BM)->(LFace->BM) + -- Opposite Face
    (LFace->BR)->(LFace->BR) + -- Opposite Face
    (RFace->TL)->(RFace->TR) + -- Current Face
    (RFace->TM)->(RFace->MR) + -- Current Face
    (RFace->TR)->(RFace->BR) + -- Current Face
    (RFace->ML)->(RFace->TM) + -- Current Face
    (RFace->MR)->(RFace->BM) + -- Current Face
    (RFace->BL)->(RFace->TL) + -- Current Face
    (RFace->BM)->(RFace->ML) + -- Current Face
    (RFace->BR)->(RFace->BL) + -- Current Face
    (BFace->TL)->(BFace->TL) +
    (BFace->TM)->(BFace->TM) +
    (BFace->TR)->(BFace->TR) +
    (BFace->ML)->(BFace->ML) +
    (BFace->MR)->(BFace->MR) +
    (BFace->BL)->(BFace->BL) +
    (BFace->BM)->(BFace->BM) +
    (BFace->BR)->(BFace->BR) +
    (DFace->TL)->(DFace->TL) +
    (DFace->TM)->(DFace->TM) +
    (DFace->TR)->(DFace->TR) +
    (DFace->ML)->(DFace->ML) +
    (DFace->MR)->(DFace->MR) +
    (DFace->BL)->(DFace->BL) +
    (DFace->BM)->(DFace->BM) +
    (DFace->BR)->(DFace->BR)

    --- BFace Rotations
    BFace.rot =
    (UFace->TL)->(UFace->TL) +
    (UFace->TM)->(UFace->TM) +
    (UFace->TR)->(UFace->TR) +
    (UFace->ML)->(UFace->ML) +
    (UFace->MR)->(UFace->MR) +
    (UFace->BL)->(UFace->BL) +
    (UFace->BM)->(UFace->BM) +
    (UFace->BR)->(UFace->BR) +
    (FFace->TL)->(FFace->TL) + -- Opposite Face
    (FFace->TM)->(FFace->TM) + -- Opposite Face
    (FFace->TR)->(FFace->TR) + -- Opposite Face
    (FFace->ML)->(FFace->ML) + -- Opposite Face
    (FFace->MR)->(FFace->MR) + -- Opposite Face
    (FFace->BL)->(FFace->BL) + -- Opposite Face
    (FFace->BM)->(FFace->BM) + -- Opposite Face
    (FFace->BR)->(FFace->BR) + -- Opposite Face
    (LFace->TL)->(LFace->TL) +
    (LFace->TM)->(LFace->TM) +
    (LFace->TR)->(LFace->TR) +
    (LFace->ML)->(LFace->ML) +
    (LFace->MR)->(LFace->MR) +
    (LFace->BL)->(LFace->BL) +
    (LFace->BM)->(LFace->BM) +
    (LFace->BR)->(LFace->BR) +
    (RFace->TL)->(RFace->TL) +
    (RFace->TM)->(RFace->TM) +
    (RFace->TR)->(RFace->TR) +
    (RFace->ML)->(RFace->ML) +
    (RFace->MR)->(RFace->MR) +
    (RFace->BL)->(RFace->BL) +
    (RFace->BM)->(RFace->BM) +
    (RFace->BR)->(RFace->BR) +
    (BFace->TL)->(BFace->TR) + -- Current Face
    (BFace->TM)->(BFace->MR) + -- Current Face
    (BFace->TR)->(BFace->BR) + -- Current Face
    (BFace->ML)->(BFace->TM) + -- Current Face
    (BFace->MR)->(BFace->BM) + -- Current Face
    (BFace->BL)->(BFace->TL) + -- Current Face
    (BFace->BM)->(BFace->ML) + -- Current Face
    (BFace->BR)->(BFace->BL) + -- Current Face
    (DFace->TL)->(DFace->TL) +
    (DFace->TM)->(DFace->TM) +
    (DFace->TR)->(DFace->TR) +
    (DFace->ML)->(DFace->ML) +
    (DFace->MR)->(DFace->MR) +
    (DFace->BL)->(DFace->BL) +
    (DFace->BM)->(DFace->BM) +
    (DFace->BR)->(DFace->BR)

    --- DFace Rotations
    DFace.rot =
    (UFace->TL)->(UFace->TL) + -- Opposite Face
    (UFace->TM)->(UFace->TM) + -- Opposite Face
    (UFace->TR)->(UFace->TR) + -- Opposite Face
    (UFace->ML)->(UFace->ML) + -- Opposite Face
    (UFace->MR)->(UFace->MR) + -- Opposite Face
    (UFace->BL)->(UFace->BL) + -- Opposite Face
    (UFace->BM)->(UFace->BM) + -- Opposite Face
    (UFace->BR)->(UFace->BR) + -- Opposite Face
    (FFace->TL)->(FFace->TL) +
    (FFace->TM)->(FFace->TM) +
    (FFace->TR)->(FFace->TR) +
    (FFace->ML)->(FFace->ML) +
    (FFace->MR)->(FFace->MR) +
    (FFace->BL)->(FFace->BL) +
    (FFace->BM)->(FFace->BM) +
    (FFace->BR)->(FFace->BR) +
    (LFace->TL)->(LFace->TL) +
    (LFace->TM)->(LFace->TM) +
    (LFace->TR)->(LFace->TR) +
    (LFace->ML)->(LFace->ML) +
    (LFace->MR)->(LFace->MR) +
    (LFace->BL)->(LFace->BL) +
    (LFace->BM)->(LFace->BM) +
    (LFace->BR)->(LFace->BR) +
    (RFace->TL)->(RFace->TL) +
    (RFace->TM)->(RFace->TM) +
    (RFace->TR)->(RFace->TR) +
    (RFace->ML)->(RFace->ML) +
    (RFace->MR)->(RFace->MR) +
    (RFace->BL)->(RFace->BL) +
    (RFace->BM)->(RFace->BM) +
    (RFace->BR)->(RFace->BR) +
    (BFace->TL)->(BFace->TL) +
    (BFace->TM)->(BFace->TM) +
    (BFace->TR)->(BFace->TR) +
    (BFace->ML)->(BFace->ML) +
    (BFace->MR)->(BFace->MR) +
    (BFace->BL)->(BFace->BL) +
    (BFace->BM)->(BFace->BM) +
    (BFace->BR)->(BFace->BR) +
    (DFace->TL)->(DFace->TR) + -- Current Face
    (DFace->TM)->(DFace->MR) + -- Current Face
    (DFace->TR)->(DFace->BR) + -- Current Face
    (DFace->ML)->(DFace->TM) + -- Current Face
    (DFace->MR)->(DFace->BM) + -- Current Face
    (DFace->BL)->(DFace->TL) + -- Current Face
    (DFace->BM)->(DFace->ML) + -- Current Face
    (DFace->BR)->(DFace->BL)   -- Current Face
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

pred rotations {
    rot =
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