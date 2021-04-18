#lang forge

option problem_type temporal
-- option min_tracelength 4
option max_tracelength 27

abstract sig Color {}
one sig White, Green, Orange, Red, Blue, Yellow extends Color {}

abstract sig Position {}
one sig TL, TM, TR, ML, MR, BL, BM, BR extends Position {}

abstract sig Face {
	center: one Color,
	var stickers: set Position->Color,
	/*
	toup: one Face,
	todown: one Face,
	toleft: one Face,
	toright: one Face,
	*/
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

/*
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
*/

pred basics {
	--orientations
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

    all c : Color | {
        all p : Position | {
            -- Each color should have one and only one sticker in each position
            one (stickers.c).p
        }
    }
}

-- Tests for stickers
pred faceEightStickers {
    all f : Face | {
        #(f.stickers) = 8
    }
}

pred colorEightStickers {
    all c : Color | {
        #(stickers.c) = 8
    }
}

pred colorStickersRightPosition {
    all c : Color | {
        all p : Position | {
            -- Each color should have one and only one sticker in each position
            one (stickers.c).p
        }
    }
}

test expect {
	eightStickersPerFace : {basics implies faceEightStickers} is theorem
    eightStickersPerColor : {basics implies faceEightStickers} is theorem
}

pred solved {
	all face: Face | {
		face.stickers[Position] = face.center
	}
}

pred solved_stutter {
	solved
	stickers' = stickers
}

-- converting these into tests for regular solver
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
    always(solved iff solved_stutter)
}
/*
-- This does not terminate!!
test expect {
	tracesEightStickersPerFace : {traces implies always faceEightStickers} is theorem
    tracesEightStickersPerColor : {traces implies always faceEightStickers} is theorem
    tracesEightStickersRightPosition : {traces implies always colorStickersRightPosition} is theorem
}
*/
pred scramble {
	basics
	solved
	eventually(always(not solved))
	always(some f: Face | rotate[f] or counter_rotate[f])
	--always(all f: Face | rotate[f] implies not after counter_rotate[f])
	--always(all f: Face | counter_rotate[f] implies not after rotate[f])
}

-- Scramble used: R U
pred sticker_based_2_step_scramble {
	get_sticker_color[stickers, UFace->TL] = White
	get_sticker_color[stickers, UFace->TM] = White
	get_sticker_color[stickers, UFace->TR] = White
	get_sticker_color[stickers, UFace->ML] = White
	get_sticker_color[stickers, UFace->MR] = White
	get_sticker_color[stickers, UFace->BL] = Green
	get_sticker_color[stickers, UFace->BM] = Green
	get_sticker_color[stickers, UFace->BR] = Green
	get_sticker_color[stickers, LFace->TL] = Green
	get_sticker_color[stickers, LFace->TM] = Green
	get_sticker_color[stickers, LFace->TR] = Yellow
	get_sticker_color[stickers, LFace->ML] = Orange
	get_sticker_color[stickers, LFace->MR] = Orange
	get_sticker_color[stickers, LFace->BL] = Orange
	get_sticker_color[stickers, LFace->BM] = Orange
	get_sticker_color[stickers, LFace->BR] = Orange
	get_sticker_color[stickers, FFace->TL] = Red
	get_sticker_color[stickers, FFace->TM] = Red
	get_sticker_color[stickers, FFace->TR] = Red
	get_sticker_color[stickers, FFace->ML] = Green
	get_sticker_color[stickers, FFace->MR] = Yellow
	get_sticker_color[stickers, FFace->BL] = Green
	get_sticker_color[stickers, FFace->BM] = Green
	get_sticker_color[stickers, FFace->BR] = Yellow
	get_sticker_color[stickers, RFace->TL] = White
	get_sticker_color[stickers, RFace->TM] = Blue
	get_sticker_color[stickers, RFace->TR] = Blue
	get_sticker_color[stickers, RFace->ML] = Red
	get_sticker_color[stickers, RFace->MR] = Red
	get_sticker_color[stickers, RFace->BL] = Red
	get_sticker_color[stickers, RFace->BM] = Red
	get_sticker_color[stickers, RFace->BR] = Red
	get_sticker_color[stickers, BFace->TL] = Orange
	get_sticker_color[stickers, BFace->TM] = Orange
	get_sticker_color[stickers, BFace->TR] = Orange
	get_sticker_color[stickers, BFace->ML] = White
	get_sticker_color[stickers, BFace->MR] = Blue
	get_sticker_color[stickers, BFace->BL] = White
	get_sticker_color[stickers, BFace->BM] = Blue
	get_sticker_color[stickers, BFace->BR] = Blue
	get_sticker_color[stickers, DFace->TL] = Yellow
	get_sticker_color[stickers, DFace->TM] = Yellow
	get_sticker_color[stickers, DFace->TR] = Blue
	get_sticker_color[stickers, DFace->ML] = Yellow
	get_sticker_color[stickers, DFace->MR] = Blue
	get_sticker_color[stickers, DFace->BL] = Yellow
	get_sticker_color[stickers, DFace->BM] = Yellow
	get_sticker_color[stickers, DFace->BR] = Blue
}

-- WARNING:
-- The predicate below requires some changes to our predicates as they are currently defined
-- We should discuss which version we like more next time we meet!
pred move_based_2_step_scramble {
	solved
	rotate[RFace]
	after rotate[UFace]
}

-- Scramble used: R L U R D'
pred sticker_based_5_step_scramble {
	get_sticker_color[stickers, UFace->TL] = Blue
	get_sticker_color[stickers, UFace->TM] = Blue
	get_sticker_color[stickers, UFace->TR] = Red
	get_sticker_color[stickers, UFace->ML] = White
	get_sticker_color[stickers, UFace->MR] = Yellow
	get_sticker_color[stickers, UFace->BL] = Green
	get_sticker_color[stickers, UFace->BM] = Green
	get_sticker_color[stickers, UFace->BR] = Yellow
	get_sticker_color[stickers, LFace->TL] = White
	get_sticker_color[stickers, LFace->TM] = Green
	get_sticker_color[stickers, LFace->TR] = Yellow
	get_sticker_color[stickers, LFace->ML] = Orange
	get_sticker_color[stickers, LFace->MR] = Orange
	get_sticker_color[stickers, LFace->BL] = White
	get_sticker_color[stickers, LFace->BM] = Green
	get_sticker_color[stickers, LFace->BR] = Blue
	get_sticker_color[stickers, FFace->TL] = Red
	get_sticker_color[stickers, FFace->TM] = Red
	get_sticker_color[stickers, FFace->TR] = Blue
	get_sticker_color[stickers, FFace->ML] = White
	get_sticker_color[stickers, FFace->MR] = Blue
	get_sticker_color[stickers, FFace->BL] = Red
	get_sticker_color[stickers, FFace->BM] = Red
	get_sticker_color[stickers, FFace->BR] = Yellow
	get_sticker_color[stickers, RFace->TL] = Red
	get_sticker_color[stickers, RFace->TM] = Red
	get_sticker_color[stickers, RFace->TR] = White
	get_sticker_color[stickers, RFace->ML] = Red
	get_sticker_color[stickers, RFace->MR] = Blue
	get_sticker_color[stickers, RFace->BL] = Blue
	get_sticker_color[stickers, RFace->BM] = Blue
	get_sticker_color[stickers, RFace->BR] = Yellow
	get_sticker_color[stickers, BFace->TL] = Green
	get_sticker_color[stickers, BFace->TM] = Orange
	get_sticker_color[stickers, BFace->TR] = Orange
	get_sticker_color[stickers, BFace->ML] = White
	get_sticker_color[stickers, BFace->MR] = Yellow
	get_sticker_color[stickers, BFace->BL] = Orange
	get_sticker_color[stickers, BFace->BM] = Orange
	get_sticker_color[stickers, BFace->BR] = Orange
	get_sticker_color[stickers, DFace->TL] = White
	get_sticker_color[stickers, DFace->TM] = White
	get_sticker_color[stickers, DFace->TR] = Orange
	get_sticker_color[stickers, DFace->ML] = Yellow
	get_sticker_color[stickers, DFace->MR] = Yellow
	get_sticker_color[stickers, DFace->BL] = Green
	get_sticker_color[stickers, DFace->BM] = Green
	get_sticker_color[stickers, DFace->BR] = Green
}

-- Scramble used: U' L2 R B2 L2 U R2 D2 R2 F2 R F2 U' B2 F L D'
pred sticker_based_many_step_scramble {
	get_sticker_color[stickers, UFace->TL] = Green
	get_sticker_color[stickers, UFace->TM] = Yellow
	get_sticker_color[stickers, UFace->TR] = White
	get_sticker_color[stickers, UFace->ML] = Yellow
	get_sticker_color[stickers, UFace->MR] = Green
	get_sticker_color[stickers, UFace->BL] = Yellow
	get_sticker_color[stickers, UFace->BM] = Red
	get_sticker_color[stickers, UFace->BR] = Green
	get_sticker_color[stickers, LFace->TL] = White
	get_sticker_color[stickers, LFace->TM] = Orange
	get_sticker_color[stickers, LFace->TR] = Orange
	get_sticker_color[stickers, LFace->ML] = Blue
	get_sticker_color[stickers, LFace->MR] = Blue
	get_sticker_color[stickers, LFace->BL] = Yellow
	get_sticker_color[stickers, LFace->BM] = Yellow
	get_sticker_color[stickers, LFace->BR] = Orange
	get_sticker_color[stickers, FFace->TL] = Blue
	get_sticker_color[stickers, FFace->TM] = Blue
	get_sticker_color[stickers, FFace->TR] = White
	get_sticker_color[stickers, FFace->ML] = White
	get_sticker_color[stickers, FFace->MR] = Orange
	get_sticker_color[stickers, FFace->BL] = Green
	get_sticker_color[stickers, FFace->BM] = Orange
	get_sticker_color[stickers, FFace->BR] = White
	get_sticker_color[stickers, RFace->TL] = Orange
	get_sticker_color[stickers, RFace->TM] = Red
	get_sticker_color[stickers, RFace->TR] = Red
	get_sticker_color[stickers, RFace->ML] = White
	get_sticker_color[stickers, RFace->MR] = Orange
	get_sticker_color[stickers, RFace->BL] = Orange
	get_sticker_color[stickers, RFace->BM] = Green
	get_sticker_color[stickers, RFace->BR] = Red
	get_sticker_color[stickers, BFace->TL] = Blue
	get_sticker_color[stickers, BFace->TM] = Green
	get_sticker_color[stickers, BFace->TR] = Red
	get_sticker_color[stickers, BFace->ML] = Blue
	get_sticker_color[stickers, BFace->MR] = Yellow
	get_sticker_color[stickers, BFace->BL] = Blue
	get_sticker_color[stickers, BFace->BM] = White
	get_sticker_color[stickers, BFace->BR] = Red
	get_sticker_color[stickers, DFace->TL] = Yellow
	get_sticker_color[stickers, DFace->TM] = Green
	get_sticker_color[stickers, DFace->TR] = Blue
	get_sticker_color[stickers, DFace->ML] = Red
	get_sticker_color[stickers, DFace->MR] = White
	get_sticker_color[stickers, DFace->BL] = Green
	get_sticker_color[stickers, DFace->BM] = Red
	get_sticker_color[stickers, DFace->BR] = Yellow
}

/** PROPERTY VERIFICATION TESTS **/

test expect {
	eightStickersPerFace : { basics implies (all f : Face | #(f.stickers) = 8) } is theorem

    -- this involves higher-order quantification? (not sure but Pardinus CLI obtained)
    -- eightStickersForEachColor : {scramble implies (all c : Color | #(Face.stickers.c) = 8)} is theorem

    anyMoveDoneFourTimesGivesSameCube : { always basics implies { {
        rotate[RFace]
        after rotate[RFace]
        after after rotate[RFace]
        after after after rotate[RFace]
    } =>  stickers'''' = stickers } } is theorem

    doAndUndoRotationGivesSameCube : {  { 
        always basics
        rotate[UFace]
        after counter_rotate[UFace]
    } => stickers'' = stickers } is theorem
    
    oppositeFaceDoesntChangeWithOverallRotation : {
        {
            basics
            rotate[LFace]
        } => dontChangeFacePlane[RFace]
    } is theorem

    sameFacePositionChangesWithOverallRotation : {
        {
            basics
            rotate[RFace]
        } => rotateFacePlane[RFace]
    } is theorem

    // properties to preserve across moves -- 

    --alwaysEightStickersForEachColor : {scramble implies always correctNumStickers} is theorem

}

--run { traces sticker_based_5_step_scramble }
