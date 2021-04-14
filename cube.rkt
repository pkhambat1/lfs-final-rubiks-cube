#lang forge

option problem_type temporal
-- option min_tracelength 4
option max_tracelength 4

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
	rot: set Face->Position->Face->Position
}

one sig UFace, FFace, LFace, RFace, BFace, DFace extends Face {}

-- stickers: Face->Position->Color
-- stickers[Face->Position] --> gives us the color

fun get_sticker_color[sticks: Face->Position->Color, fp: Face->Position]: Color {
	{ (fp.Position).sticks[Face.fp] }
}

pred rotate[rf: Face] {
    all f: Face | {
        all p: Position | {
            get_sticker_color[stickers, f->p] = get_sticker_color[stickers', rf.rot[f][p]]
        }
    }
}

pred counter_rotate[rf: Face] {
    all f: Face | {
        all p: Position | {
            get_sticker_color[stickers', f->p] = get_sticker_color[stickers, rf.rot[f][p]]
        }
    }
}

/*
-- helper transition preds
-- use for rotating face
pred rotateFacePlane[f: Face] {
    -- positions are TL, TM, TR, ML, MR, BL, BM, BR
    -- f.stickers is Position->Color
    -- f.stickers[Position] is Color
    -- f.stickers.Color is position
    f.stickers[TL] = f.(stickers')[TR]
    f.stickers[TM] = f.(stickers')[MR]
    f.stickers[TR] = f.(stickers')[BR]
    f.stickers[MR] = f.(stickers')[BM]
    f.stickers[BR] = f.(stickers')[BL]
    f.stickers[BM] = f.(stickers')[ML]
    f.stickers[BL] = f.(stickers')[TL]
    f.stickers[ML] = f.(stickers')[TM]
}

-- use for opposite of rotating face
pred dontChangeFacePlane[f: Face] {
    -- f.stickers is Position->Color
    f.stickers' = f.stickers
}
*/

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
    (UFace->BL)->(RFace->TL) + --
    (UFace->BM)->(RFace->ML) + --
    (UFace->BR)->(RFace->BL) + --
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
    (LFace->TR)->(UFace->BR) + --
    (LFace->ML)->(LFace->ML) +
    (LFace->MR)->(UFace->BM) + --
    (LFace->BL)->(LFace->BL) +
    (LFace->BM)->(LFace->BM) +
    (LFace->BR)->(UFace->BL) + --
    (RFace->TL)->(DFace->TR) + --
    (RFace->TM)->(RFace->TM) +
    (RFace->TR)->(RFace->TR) +
    (RFace->ML)->(DFace->TM) + --
    (RFace->MR)->(RFace->MR) +
    (RFace->BL)->(DFace->TL) + --
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
    (DFace->TL)->(LFace->TR) + --
    (DFace->TM)->(LFace->MR) + --
    (DFace->TR)->(LFace->BR) + --
    (DFace->ML)->(DFace->ML) +
    (DFace->MR)->(DFace->MR) +
    (DFace->BL)->(DFace->BL) +
    (DFace->BM)->(DFace->BM) +
    (DFace->BR)->(DFace->BR)

    --- LFace Rotations
    LFace.rot =
    (UFace->TL)->(FFace->TL) + --
    (UFace->TM)->(UFace->TM) +
    (UFace->TR)->(UFace->TR) +
    (UFace->ML)->(FFace->ML) + --
    (UFace->MR)->(UFace->MR) +
    (UFace->BL)->(FFace->BL) + --
    (UFace->BM)->(UFace->BM) +
    (UFace->BR)->(UFace->BR) +
    (FFace->TL)->(DFace->TL) + --
    (FFace->TM)->(FFace->TM) +
    (FFace->TR)->(FFace->TR) +
    (FFace->ML)->(DFace->ML) + --
    (FFace->MR)->(FFace->MR) +
    (FFace->BL)->(DFace->BL) + --
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
    (BFace->TR)->(UFace->BL) + --
    (BFace->ML)->(BFace->ML) +
    (BFace->MR)->(UFace->ML) + --
    (BFace->BL)->(BFace->BL) +
    (BFace->BM)->(BFace->BM) +
    (BFace->BR)->(UFace->TL) + --
    (DFace->TL)->(BFace->BR) + --
    (DFace->TM)->(DFace->TM) +
    (DFace->TR)->(DFace->TR) +
    (DFace->ML)->(BFace->MR) + --
    (DFace->MR)->(DFace->MR) +
    (DFace->BL)->(BFace->TR) + --
    (DFace->BM)->(DFace->BM) +
    (DFace->BR)->(DFace->BR)

    --- RFace Rotations
    RFace.rot =
    (UFace->TL)->(UFace->TL) +
    (UFace->TM)->(UFace->TM) +
    (UFace->TR)->(BFace->BL) + --
    (UFace->ML)->(UFace->ML) +
    (UFace->MR)->(BFace->ML) + --
    (UFace->BL)->(UFace->BL) +
    (UFace->BM)->(UFace->BM) +
    (UFace->BR)->(BFace->TL) + --
    (FFace->TL)->(FFace->TL) +
    (FFace->TM)->(FFace->TM) +
    (FFace->TR)->(UFace->TR) + --
    (FFace->ML)->(FFace->ML) +
    (FFace->MR)->(UFace->MR) + --
    (FFace->BL)->(FFace->BL) +
    (FFace->BM)->(FFace->BM) +
    (FFace->BR)->(UFace->BR) + --
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
    (BFace->TL)->(DFace->BR) + --
    (BFace->TM)->(BFace->TM) +
    (BFace->TR)->(BFace->TR) +
    (BFace->ML)->(DFace->MR) + --
    (BFace->MR)->(BFace->MR) +
    (BFace->BL)->(DFace->TR) + --
    (BFace->BM)->(BFace->BM) +
    (BFace->BR)->(BFace->BR) +
    (DFace->TL)->(DFace->TL) +
    (DFace->TM)->(DFace->TM) +
    (DFace->TR)->(FFace->TR) + --
    (DFace->ML)->(DFace->ML) +
    (DFace->MR)->(FFace->MR) + --
    (DFace->BL)->(DFace->BL) +
    (DFace->BM)->(DFace->BM) +
    (DFace->BR)->(FFace->BR)   --

    --- BFace Rotations
    BFace.rot =
    (UFace->TL)->(LFace->BL) + --
    (UFace->TM)->(LFace->ML) + --
    (UFace->TR)->(LFace->TL) + --
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
    (LFace->TL)->(DFace->BL) + --
    (LFace->TM)->(LFace->TM) +
    (LFace->TR)->(LFace->TR) +
    (LFace->ML)->(DFace->BM) + --
    (LFace->MR)->(LFace->MR) +
    (LFace->BL)->(DFace->BR) + --
    (LFace->BM)->(LFace->BM) +
    (LFace->BR)->(LFace->BR) +
    (RFace->TL)->(RFace->TL) +
    (RFace->TM)->(RFace->TM) +
    (RFace->TR)->(UFace->TL) + --
    (RFace->ML)->(RFace->ML) +
    (RFace->MR)->(UFace->TM) + --
    (RFace->BL)->(RFace->BL) +
    (RFace->BM)->(RFace->BM) +
    (RFace->BR)->(UFace->TR) + --
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
    (DFace->BL)->(RFace->BR) + --
    (DFace->BM)->(RFace->MR) + --
    (DFace->BR)->(RFace->TR)   --

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
    (FFace->BL)->(RFace->BL) + --
    (FFace->BM)->(RFace->BM) + --
    (FFace->BR)->(RFace->BR) + --
    (LFace->TL)->(LFace->TL) +
    (LFace->TM)->(LFace->TM) +
    (LFace->TR)->(LFace->TR) +
    (LFace->ML)->(LFace->ML) +
    (LFace->MR)->(LFace->MR) +
    (LFace->BL)->(FFace->BL) + --
    (LFace->BM)->(FFace->BM) + --
    (LFace->BR)->(FFace->BR) + --
    (RFace->TL)->(RFace->TL) +
    (RFace->TM)->(RFace->TM) +
    (RFace->TR)->(RFace->TR) +
    (RFace->ML)->(RFace->ML) +
    (RFace->MR)->(RFace->MR) +
    (RFace->BL)->(BFace->BL) + --
    (RFace->BM)->(BFace->BM) + --
    (RFace->BR)->(BFace->BR) + --
    (BFace->TL)->(BFace->TL) +
    (BFace->TM)->(BFace->TM) +
    (BFace->TR)->(BFace->TR) +
    (BFace->ML)->(BFace->ML) +
    (BFace->MR)->(BFace->MR) +
    (BFace->BL)->(LFace->BL) + --
    (BFace->BM)->(LFace->BM) + --
    (BFace->BR)->(LFace->BR) + --
    (DFace->TL)->(DFace->TR) + -- Current Face
    (DFace->TM)->(DFace->MR) + -- Current Face
    (DFace->TR)->(DFace->BR) + -- Current Face
    (DFace->ML)->(DFace->TM) + -- Current Face
    (DFace->MR)->(DFace->BM) + -- Current Face
    (DFace->BL)->(DFace->TL) + -- Current Face
    (DFace->BM)->(DFace->ML) + -- Current Face
    (DFace->BR)->(DFace->BL)   -- Current Face
}

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
	rotations

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

/*
test expect {
	eightStickersPerFace : {basics implies (all f : Face | #(f.stickers) = 8)} is theorem
}
*/

pred solved {
	all face: Face | {
		face.stickers[Position] = face.center
	}
}

pred solved_stutter {
	solved
	stickers' = stickers
}

pred less_dumb_solver {
	always(all f: Face | rotate[f] implies not after counter_rotate[f])
	always(all f: Face | counter_rotate[f] implies not after rotate[f])
	always(not solved implies stickers != stickers'''')
}

pred traces {
	basics
	less_dumb_solver
	not solved
	always(not solved iff {some f: Face | rotate[f] or counter_rotate[f]})
	always(not solved implies eventually always solved)
}

pred scramble{
	basics
	solved
	eventually(always(not solved))
	always(some f: Face | rotate[f] or counter_rotate[f])
	--always(all f: Face | rotate[f] implies not after counter_rotate[f])
	--always(all f: Face | counter_rotate[f] implies not after rotate[f])
}

-- not actually a scramble (to be fixed next time)
/*
inst two_step_scramble {
	Green = Green0
	RFace = RFace0
	FFace = FFace0
	Yellow = Yellow0
	Blue = Blue0
	UFace = UFace0
	BR = BR0
	LFace = LFace0
	Red = Red0
	BL = BL0
	White = White0
	TM = TM0
	MR = MR0
	TR = TR0
	BM = BM0
	BFace = BFace0
	Orange = Orange0
	TL = TL0
	DFace = DFace0
	ML = ML0
	Color = Green0 + Yellow0 + Blue0 + Red0 + White0 + Orange0
	Face = RFace0 + FFace0 + UFace0 + LFace0 + BFace0 + DFace0
	Position = BR0 + BL0 + TM0 + MR0 + TR0 + BM0 + TL0 + ML0
	rot = UFace0->UFace0->TL0->UFace0->TR0 + UFace0->UFace0->TM0->UFace0->MR0 + UFace0->UFace0->TR0->UFace0->BR0 + UFace0->UFace0->ML0->UFace0->TM0 + UFace0->UFace0->MR0->UFace0->BM0 + UFace0->UFace0->BL0->UFace0->TL0 + UFace0->UFace0->BM0->UFace0->ML0 + UFace0->UFace0->BR0->UFace0->BL0 + UFace0->FFace0->TL0->LFace0->TL0 + UFace0->FFace0->TM0->LFace0->TM0 + UFace0->FFace0->TR0->LFace0->TR0 + UFace0->FFace0->ML0->FFace0->ML0 + UFace0->FFace0->MR0->FFace0->MR0 + UFace0->FFace0->BL0->FFace0->BL0 + UFace0->FFace0->BM0->FFace0->BM0 + UFace0->FFace0->BR0->FFace0->BR0 + UFace0->LFace0->TL0->BFace0->TL0 + UFace0->LFace0->TM0->BFace0->TM0 + UFace0->LFace0->TR0->BFace0->TR0 + UFace0->LFace0->ML0->LFace0->ML0 + UFace0->LFace0->MR0->LFace0->MR0 + UFace0->LFace0->BL0->LFace0->BL0 + UFace0->LFace0->BM0->LFace0->BM0 + UFace0->LFace0->BR0->LFace0->BR0 + UFace0->RFace0->TL0->FFace0->TL0 + UFace0->RFace0->TM0->FFace0->TM0 + UFace0->RFace0->TR0->FFace0->TR0 + UFace0->RFace0->ML0->RFace0->ML0 + UFace0->RFace0->MR0->RFace0->MR0 + UFace0->RFace0->BL0->RFace0->BL0 + UFace0->RFace0->BM0->RFace0->BM0 + UFace0->RFace0->BR0->RFace0->BR0 + UFace0->BFace0->TL0->RFace0->TL0 + UFace0->BFace0->TM0->RFace0->TM0 + UFace0->BFace0->TR0->RFace0->TR0 + UFace0->BFace0->ML0->BFace0->ML0 + UFace0->BFace0->MR0->BFace0->MR0 + UFace0->BFace0->BL0->BFace0->BL0 + UFace0->BFace0->BM0->BFace0->BM0 + UFace0->BFace0->BR0->BFace0->BR0 + UFace0->DFace0->TL0->DFace0->TL0 + UFace0->DFace0->TM0->DFace0->TM0 + UFace0->DFace0->TR0->DFace0->TR0 + UFace0->DFace0->ML0->DFace0->ML0 + UFace0->DFace0->MR0->DFace0->MR0 + UFace0->DFace0->BL0->DFace0->BL0 + UFace0->DFace0->BM0->DFace0->BM0 + UFace0->DFace0->BR0->DFace0->BR0 + FFace0->UFace0->TL0->UFace0->TL0 + FFace0->UFace0->TM0->UFace0->TM0 + FFace0->UFace0->TR0->UFace0->TR0 + FFace0->UFace0->ML0->UFace0->ML0 + FFace0->UFace0->MR0->UFace0->MR0 + FFace0->UFace0->BL0->RFace0->TL0 + FFace0->UFace0->BM0->RFace0->ML0 + FFace0->UFace0->BR0->RFace0->BL0 + FFace0->FFace0->TL0->FFace0->TR0 + FFace0->FFace0->TM0->FFace0->MR0 + FFace0->FFace0->TR0->FFace0->BR0 + FFace0->FFace0->ML0->FFace0->TM0 + FFace0->FFace0->MR0->FFace0->BM0 + FFace0->FFace0->BL0->FFace0->TL0 + FFace0->FFace0->BM0->FFace0->ML0 + FFace0->FFace0->BR0->FFace0->BL0 + FFace0->LFace0->TL0->LFace0->TL0 + FFace0->LFace0->TM0->LFace0->TM0 + FFace0->LFace0->TR0->UFace0->BR0 + FFace0->LFace0->ML0->LFace0->ML0 + FFace0->LFace0->MR0->UFace0->BM0 + FFace0->LFace0->BL0->LFace0->BL0 + FFace0->LFace0->BM0->LFace0->BM0 + FFace0->LFace0->BR0->UFace0->BL0 + FFace0->RFace0->TL0->DFace0->TR0 + FFace0->RFace0->TM0->RFace0->TM0 + FFace0->RFace0->TR0->RFace0->TR0 + FFace0->RFace0->ML0->DFace0->TM0 + FFace0->RFace0->MR0->RFace0->MR0 + FFace0->RFace0->BL0->DFace0->TL0 + FFace0->RFace0->BM0->RFace0->BM0 + FFace0->RFace0->BR0->RFace0->BR0 + FFace0->BFace0->TL0->BFace0->TL0 + FFace0->BFace0->TM0->BFace0->TM0 + FFace0->BFace0->TR0->BFace0->TR0 + FFace0->BFace0->ML0->BFace0->ML0 + FFace0->BFace0->MR0->BFace0->MR0 + FFace0->BFace0->BL0->BFace0->BL0 + FFace0->BFace0->BM0->BFace0->BM0 + FFace0->BFace0->BR0->BFace0->BR0 + FFace0->DFace0->TL0->LFace0->TR0 + FFace0->DFace0->TM0->LFace0->MR0 + FFace0->DFace0->TR0->LFace0->BR0 + FFace0->DFace0->ML0->DFace0->ML0 + FFace0->DFace0->MR0->DFace0->MR0 + FFace0->DFace0->BL0->DFace0->BL0 + FFace0->DFace0->BM0->DFace0->BM0 + FFace0->DFace0->BR0->DFace0->BR0 + LFace0->UFace0->TL0->FFace0->TL0 + LFace0->UFace0->TM0->UFace0->TM0 + LFace0->UFace0->TR0->UFace0->TR0 + LFace0->UFace0->ML0->FFace0->ML0 + LFace0->UFace0->MR0->UFace0->MR0 + LFace0->UFace0->BL0->FFace0->BL0 + LFace0->UFace0->BM0->UFace0->BM0 + LFace0->UFace0->BR0->UFace0->BR0 + LFace0->FFace0->TL0->DFace0->TL0 + LFace0->FFace0->TM0->FFace0->TM0 + LFace0->FFace0->TR0->FFace0->TR0 + LFace0->FFace0->ML0->DFace0->ML0 + LFace0->FFace0->MR0->FFace0->MR0 + LFace0->FFace0->BL0->DFace0->BL0 + LFace0->FFace0->BM0->FFace0->BM0 + LFace0->FFace0->BR0->FFace0->BR0 + LFace0->LFace0->TL0->LFace0->TR0 + LFace0->LFace0->TM0->LFace0->MR0 + LFace0->LFace0->TR0->LFace0->BR0 + LFace0->LFace0->ML0->LFace0->TM0 + LFace0->LFace0->MR0->LFace0->BM0 + LFace0->LFace0->BL0->LFace0->TL0 + LFace0->LFace0->BM0->LFace0->ML0 + LFace0->LFace0->BR0->LFace0->BL0 + LFace0->RFace0->TL0->RFace0->TL0 + LFace0->RFace0->TM0->RFace0->TM0 + LFace0->RFace0->TR0->RFace0->TR0 + LFace0->RFace0->ML0->RFace0->ML0 + LFace0->RFace0->MR0->RFace0->MR0 + LFace0->RFace0->BL0->RFace0->BL0 + LFace0->RFace0->BM0->RFace0->BM0 + LFace0->RFace0->BR0->RFace0->BR0 + LFace0->BFace0->TL0->BFace0->TL0 + LFace0->BFace0->TM0->BFace0->TM0 + LFace0->BFace0->TR0->UFace0->BL0 + LFace0->BFace0->ML0->BFace0->ML0 + LFace0->BFace0->MR0->UFace0->ML0 + LFace0->BFace0->BL0->BFace0->BL0 + LFace0->BFace0->BM0->BFace0->BM0 + LFace0->BFace0->BR0->UFace0->TL0 + LFace0->DFace0->TL0->BFace0->BR0 + LFace0->DFace0->TM0->DFace0->TM0 + LFace0->DFace0->TR0->DFace0->TR0 + LFace0->DFace0->ML0->BFace0->MR0 + LFace0->DFace0->MR0->DFace0->MR0 + LFace0->DFace0->BL0->BFace0->TR0 + LFace0->DFace0->BM0->DFace0->BM0 + LFace0->DFace0->BR0->DFace0->BR0 + RFace0->UFace0->TL0->UFace0->TL0 + RFace0->UFace0->TM0->UFace0->TM0 + RFace0->UFace0->TR0->BFace0->BL0 + RFace0->UFace0->ML0->UFace0->ML0 + RFace0->UFace0->MR0->BFace0->ML0 + RFace0->UFace0->BL0->UFace0->BL0 + RFace0->UFace0->BM0->UFace0->BM0 + RFace0->UFace0->BR0->BFace0->TL0 + RFace0->FFace0->TL0->FFace0->TL0 + RFace0->FFace0->TM0->FFace0->TM0 + RFace0->FFace0->TR0->UFace0->TR0 + RFace0->FFace0->ML0->FFace0->ML0 + RFace0->FFace0->MR0->UFace0->MR0 + RFace0->FFace0->BL0->FFace0->BL0 + RFace0->FFace0->BM0->FFace0->BM0 + RFace0->FFace0->BR0->UFace0->BR0 + RFace0->LFace0->TL0->LFace0->TL0 + RFace0->LFace0->TM0->LFace0->TM0 + RFace0->LFace0->TR0->LFace0->TR0 + RFace0->LFace0->ML0->LFace0->ML0 + RFace0->LFace0->MR0->LFace0->MR0 + RFace0->LFace0->BL0->LFace0->BL0 + RFace0->LFace0->BM0->LFace0->BM0 + RFace0->LFace0->BR0->LFace0->BR0 + RFace0->RFace0->TL0->RFace0->TR0 + RFace0->RFace0->TM0->RFace0->MR0 + RFace0->RFace0->TR0->RFace0->BR0 + RFace0->RFace0->ML0->RFace0->TM0 + RFace0->RFace0->MR0->RFace0->BM0 + RFace0->RFace0->BL0->RFace0->TL0 + RFace0->RFace0->BM0->RFace0->ML0 + RFace0->RFace0->BR0->RFace0->BL0 + RFace0->BFace0->TL0->DFace0->BR0 + RFace0->BFace0->TM0->BFace0->TM0 + RFace0->BFace0->TR0->BFace0->TR0 + RFace0->BFace0->ML0->DFace0->MR0 + RFace0->BFace0->MR0->BFace0->MR0 + RFace0->BFace0->BL0->DFace0->TR0 + RFace0->BFace0->BM0->BFace0->BM0 + RFace0->BFace0->BR0->BFace0->BR0 + RFace0->DFace0->TL0->DFace0->TL0 + RFace0->DFace0->TM0->DFace0->TM0 + RFace0->DFace0->TR0->FFace0->TR0 + RFace0->DFace0->ML0->DFace0->ML0 + RFace0->DFace0->MR0->FFace0->MR0 + RFace0->DFace0->BL0->DFace0->BL0 + RFace0->DFace0->BM0->DFace0->BM0 + RFace0->DFace0->BR0->FFace0->BR0 + BFace0->UFace0->TL0->LFace0->BL0 + BFace0->UFace0->TM0->LFace0->ML0 + BFace0->UFace0->TR0->LFace0->TL0 + BFace0->UFace0->ML0->UFace0->ML0 + BFace0->UFace0->MR0->UFace0->MR0 + BFace0->UFace0->BL0->UFace0->BL0 + BFace0->UFace0->BM0->UFace0->BM0 + BFace0->UFace0->BR0->UFace0->BR0 + BFace0->FFace0->TL0->FFace0->TL0 + BFace0->FFace0->TM0->FFace0->TM0 + BFace0->FFace0->TR0->FFace0->TR0 + BFace0->FFace0->ML0->FFace0->ML0 + BFace0->FFace0->MR0->FFace0->MR0 + BFace0->FFace0->BL0->FFace0->BL0 + BFace0->FFace0->BM0->FFace0->BM0 + BFace0->FFace0->BR0->FFace0->BR0 + BFace0->LFace0->TL0->DFace0->BL0 + BFace0->LFace0->TM0->LFace0->TM0 + BFace0->LFace0->TR0->LFace0->TR0 + BFace0->LFace0->ML0->DFace0->BM0 + BFace0->LFace0->MR0->LFace0->MR0 + BFace0->LFace0->BL0->DFace0->BR0 + BFace0->LFace0->BM0->LFace0->BM0 + BFace0->LFace0->BR0->LFace0->BR0 + BFace0->RFace0->TL0->RFace0->TL0 + BFace0->RFace0->TM0->RFace0->TM0 + BFace0->RFace0->TR0->UFace0->TL0 + BFace0->RFace0->ML0->RFace0->ML0 + BFace0->RFace0->MR0->UFace0->TM0 + BFace0->RFace0->BL0->RFace0->BL0 + BFace0->RFace0->BM0->RFace0->BM0 + BFace0->RFace0->BR0->UFace0->TR0 + BFace0->BFace0->TL0->BFace0->TR0 + BFace0->BFace0->TM0->BFace0->MR0 + BFace0->BFace0->TR0->BFace0->BR0 + BFace0->BFace0->ML0->BFace0->TM0 + BFace0->BFace0->MR0->BFace0->BM0 + BFace0->BFace0->BL0->BFace0->TL0 + BFace0->BFace0->BM0->BFace0->ML0 + BFace0->BFace0->BR0->BFace0->BL0 + BFace0->DFace0->TL0->DFace0->TL0 + BFace0->DFace0->TM0->DFace0->TM0 + BFace0->DFace0->TR0->DFace0->TR0 + BFace0->DFace0->ML0->DFace0->ML0 + BFace0->DFace0->MR0->DFace0->MR0 + BFace0->DFace0->BL0->RFace0->BR0 + BFace0->DFace0->BM0->RFace0->MR0 + BFace0->DFace0->BR0->RFace0->TR0 + DFace0->UFace0->TL0->UFace0->TL0 + DFace0->UFace0->TM0->UFace0->TM0 + DFace0->UFace0->TR0->UFace0->TR0 + DFace0->UFace0->ML0->UFace0->ML0 + DFace0->UFace0->MR0->UFace0->MR0 + DFace0->UFace0->BL0->UFace0->BL0 + DFace0->UFace0->BM0->UFace0->BM0 + DFace0->UFace0->BR0->UFace0->BR0 + DFace0->FFace0->TL0->FFace0->TL0 + DFace0->FFace0->TM0->FFace0->TM0 + DFace0->FFace0->TR0->FFace0->TR0 + DFace0->FFace0->ML0->FFace0->ML0 + DFace0->FFace0->MR0->FFace0->MR0 + DFace0->FFace0->BL0->RFace0->BL0 + DFace0->FFace0->BM0->RFace0->BM0 + DFace0->FFace0->BR0->RFace0->BR0 + DFace0->LFace0->TL0->LFace0->TL0 + DFace0->LFace0->TM0->LFace0->TM0 + DFace0->LFace0->TR0->LFace0->TR0 + DFace0->LFace0->ML0->LFace0->ML0 + DFace0->LFace0->MR0->LFace0->MR0 + DFace0->LFace0->BL0->FFace0->BL0 + DFace0->LFace0->BM0->FFace0->BM0 + DFace0->LFace0->BR0->FFace0->BR0 + DFace0->RFace0->TL0->RFace0->TL0 + DFace0->RFace0->TM0->RFace0->TM0 + DFace0->RFace0->TR0->RFace0->TR0 + DFace0->RFace0->ML0->RFace0->ML0 + DFace0->RFace0->MR0->RFace0->MR0 + DFace0->RFace0->BL0->BFace0->BL0 + DFace0->RFace0->BM0->BFace0->BM0 + DFace0->RFace0->BR0->BFace0->BR0 + DFace0->BFace0->TL0->BFace0->TL0 + DFace0->BFace0->TM0->BFace0->TM0 + DFace0->BFace0->TR0->BFace0->TR0 + DFace0->BFace0->ML0->BFace0->ML0 + DFace0->BFace0->MR0->BFace0->MR0 + DFace0->BFace0->BL0->LFace0->BL0 + DFace0->BFace0->BM0->LFace0->BM0 + DFace0->BFace0->BR0->LFace0->BR0 + DFace0->DFace0->TL0->DFace0->TR0 + DFace0->DFace0->TM0->DFace0->MR0 + DFace0->DFace0->TR0->DFace0->BR0 + DFace0->DFace0->ML0->DFace0->TM0 + DFace0->DFace0->MR0->DFace0->BM0 + DFace0->DFace0->BL0->DFace0->TL0 + DFace0->DFace0->BM0->DFace0->ML0 + DFace0->DFace0->BR0->DFace0->BL0
	stickers = UFace0->TL0->White0 + UFace0->TM0->White0 + UFace0->TR0->White0 + UFace0->ML0->White0 + UFace0->MR0->White0 + UFace0->BL0->White0 + UFace0->BM0->White0 + UFace0->BR0->White0 + FFace0->TL0->Green0 + FFace0->TM0->Green0 + FFace0->TR0->Green0 + FFace0->ML0->Green0 + FFace0->MR0->Green0 + FFace0->BL0->Green0 + FFace0->BM0->Green0 + FFace0->BR0->Green0 + LFace0->TL0->Orange0 + LFace0->TM0->Orange0 + LFace0->TR0->Orange0 + LFace0->ML0->Orange0 + LFace0->MR0->Orange0 + LFace0->BL0->Orange0 + LFace0->BM0->Orange0 + LFace0->BR0->Orange0 + RFace0->TL0->Red0 + RFace0->TM0->Red0 + RFace0->TR0->Red0 + RFace0->ML0->Red0 + RFace0->MR0->Red0 + RFace0->BL0->Red0 + RFace0->BM0->Red0 + RFace0->BR0->Red0 + BFace0->TL0->Blue0 + BFace0->TM0->Blue0 + BFace0->TR0->Blue0 + BFace0->ML0->Blue0 + BFace0->MR0->Blue0 + BFace0->BL0->Blue0 + BFace0->BM0->Blue0 + BFace0->BR0->Blue0 + DFace0->TL0->Yellow0 + DFace0->TM0->Yellow0 + DFace0->TR0->Yellow0 + DFace0->ML0->Yellow0 + DFace0->MR0->Yellow0 + DFace0->BL0->Yellow0 + DFace0->BM0->Yellow0 + DFace0->BR0->Yellow0
	center = UFace0->White0 + FFace0->Green0 + LFace0->Orange0 + RFace0->Red0 + BFace0->Blue0 + DFace0->Yellow0
	toup = UFace0->BFace0 + FFace0->UFace0 + LFace0->UFace0 + RFace0->UFace0 + BFace0->UFace0 + DFace0->FFace0
	toright = UFace0->RFace0 + FFace0->RFace0 + LFace0->FFace0 + RFace0->BFace0 + BFace0->LFace0 + DFace0->RFace0
	todown = UFace0->FFace0 + FFace0->DFace0 + LFace0->DFace0 + RFace0->DFace0 + BFace0->DFace0 + DFace0->BFace0
	toleft = UFace0->LFace0 + FFace0->LFace0 + LFace0->BFace0 + RFace0->FFace0 + BFace0->RFace0 + DFace0->LFace0
}
*/

-- this tries to solve a scramble that is two rotations away from solved (once the instance is fixed)
-- run { traces } for two_step_scramble

run { scramble }