#lang forge
open "foundations.rkt"

--option solver MiniSat
option problem_type temporal
option max_tracelength 27

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

pred basics {
	rotations

	-- defining central colors
	UFace.center = White
	LFace.center = Orange
	FFace.center = Green
	RFace.center = Red
	BFace.center = Blue
	DFace.center = Yellow

	-- defining opposite faces
	UFace.opposite = DFace
	LFace.opposite = RFace
	FFace.opposite = BFace
	RFace.opposite = LFace
	BFace.opposite = FFace
	DFace.opposite = UFace

	-- enforces that each sticker is set to exactly one color
	all face: Face | {
		all pos: Position | {
			one face.stickers[pos]
		}
	}
	/*
    all c : Color | {
        all p : Position | {
            -- Each color should have one and only one sticker in each position
            one (stickers.c).p
        }
    }
    */
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
pred less_naive_solver {
	-- don't undo your most recent move
	--always(all f: Face | rotate[f] implies not after counter_rotate[f])
	--always(all f: Face | counter_rotate[f] implies not after rotate[f])
	-- don't repeat a state using multiple moves and their counter rotations
	always(not solved implies stickers != stickers'''')
	-- never rotate the same face more than two times in a row (three times is the same as one in the other direction)
	always(all f: Face | rotate[f] and after rotate[f] implies not after after rotate[f])
	always(all f: Face | counter_rotate[f] and after counter_rotate[f] implies not after after counter_rotate[f])
	-- don't undo a move until a face that intersects with the face is rotated
	--/*
	always(all f: Face | rotate[f] implies not counter_rotate[f] until 
		{solved or {some af: Face | {af != f.opposite and {rotate[af] or counter_rotate[af]}}}})
	always(all f: Face | counter_rotate[f] implies not rotate[f] until 
		{solved or {some af: Face | {af != f.opposite and {counter_rotate[af] or rotate[af]}}}})
	--*/
}

pred traces {
	basics
	--less_naive_solver
	not solved
	always(not solved iff {some f: Face | rotate[f] or counter_rotate[f]})
	always(not solved implies eventually always solved)
    always(solved iff solved_stutter)
}

pred scramble {
	basics
	solved
	eventually(always(not solved))
	always(some f: Face | rotate[f] or counter_rotate[f])
	--always(all f: Face | rotate[f] implies not after counter_rotate[f])
	--always(all f: Face | counter_rotate[f] implies not after rotate[f])
}

-- Scramble used: U
pred sticker_based_1_step_scramble {
	get_sticker_color[stickers, UFace->TL] = White
	get_sticker_color[stickers, UFace->TM] = White
	get_sticker_color[stickers, UFace->TR] = White
	get_sticker_color[stickers, UFace->ML] = White
	get_sticker_color[stickers, UFace->MR] = White
	get_sticker_color[stickers, UFace->BL] = White
	get_sticker_color[stickers, UFace->BM] = White
	get_sticker_color[stickers, UFace->BR] = White
	get_sticker_color[stickers, LFace->TL] = Green
	get_sticker_color[stickers, LFace->TM] = Green
	get_sticker_color[stickers, LFace->TR] = Green
	get_sticker_color[stickers, LFace->ML] = Orange
	get_sticker_color[stickers, LFace->MR] = Orange
	get_sticker_color[stickers, LFace->BL] = Orange
	get_sticker_color[stickers, LFace->BM] = Orange
	get_sticker_color[stickers, LFace->BR] = Orange
	get_sticker_color[stickers, FFace->TL] = Red
	get_sticker_color[stickers, FFace->TM] = Red
	get_sticker_color[stickers, FFace->TR] = Red
	get_sticker_color[stickers, FFace->ML] = Green
	get_sticker_color[stickers, FFace->MR] = Green
	get_sticker_color[stickers, FFace->BL] = Green
	get_sticker_color[stickers, FFace->BM] = Green
	get_sticker_color[stickers, FFace->BR] = Green
	get_sticker_color[stickers, RFace->TL] = Blue
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
	get_sticker_color[stickers, BFace->ML] = Blue
	get_sticker_color[stickers, BFace->MR] = Blue
	get_sticker_color[stickers, BFace->BL] = Blue
	get_sticker_color[stickers, BFace->BM] = Blue
	get_sticker_color[stickers, BFace->BR] = Blue
	get_sticker_color[stickers, DFace->TL] = Yellow
	get_sticker_color[stickers, DFace->TM] = Yellow
	get_sticker_color[stickers, DFace->TR] = Yellow
	get_sticker_color[stickers, DFace->ML] = Yellow
	get_sticker_color[stickers, DFace->MR] = Yellow
	get_sticker_color[stickers, DFace->BL] = Yellow
	get_sticker_color[stickers, DFace->BM] = Yellow
	get_sticker_color[stickers, DFace->BR] = Yellow
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

-- Scramble used: R U R' U'
pred sticker_based_4_step_scramble {
	get_sticker_color[stickers, UFace->TL] = White
	get_sticker_color[stickers, UFace->TM] = White
	get_sticker_color[stickers, UFace->TR] = Orange
	get_sticker_color[stickers, UFace->ML] = White
	get_sticker_color[stickers, UFace->MR] = Green
	get_sticker_color[stickers, UFace->BL] = White
	get_sticker_color[stickers, UFace->BM] = White
	get_sticker_color[stickers, UFace->BR] = Green
	get_sticker_color[stickers, LFace->TL] = Blue
	get_sticker_color[stickers, LFace->TM] = Orange
	get_sticker_color[stickers, LFace->TR] = Orange
	get_sticker_color[stickers, LFace->ML] = Orange
	get_sticker_color[stickers, LFace->MR] = Orange
	get_sticker_color[stickers, LFace->BL] = Orange
	get_sticker_color[stickers, LFace->BM] = Orange
	get_sticker_color[stickers, LFace->BR] = Orange
	get_sticker_color[stickers, FFace->TL] = Green
	get_sticker_color[stickers, FFace->TM] = Green
	get_sticker_color[stickers, FFace->TR] = Yellow
	get_sticker_color[stickers, FFace->ML] = Green
	get_sticker_color[stickers, FFace->MR] = White
	get_sticker_color[stickers, FFace->BL] = Green
	get_sticker_color[stickers, FFace->BM] = Green
	get_sticker_color[stickers, FFace->BR] = Green
	get_sticker_color[stickers, RFace->TL] = Red
	get_sticker_color[stickers, RFace->TM] = Red
	get_sticker_color[stickers, RFace->TR] = White
	get_sticker_color[stickers, RFace->ML] = Blue
	get_sticker_color[stickers, RFace->MR] = Red
	get_sticker_color[stickers, RFace->BL] = White
	get_sticker_color[stickers, RFace->BM] = Red
	get_sticker_color[stickers, RFace->BR] = Red
	get_sticker_color[stickers, BFace->TL] = Blue
	get_sticker_color[stickers, BFace->TM] = Red
	get_sticker_color[stickers, BFace->TR] = Red
	get_sticker_color[stickers, BFace->ML] = Blue
	get_sticker_color[stickers, BFace->MR] = Blue
	get_sticker_color[stickers, BFace->BL] = Blue
	get_sticker_color[stickers, BFace->BM] = Blue
	get_sticker_color[stickers, BFace->BR] = Blue
	get_sticker_color[stickers, DFace->TL] = Yellow
	get_sticker_color[stickers, DFace->TM] = Yellow
	get_sticker_color[stickers, DFace->TR] = Red
	get_sticker_color[stickers, DFace->ML] = Yellow
	get_sticker_color[stickers, DFace->MR] = Yellow
	get_sticker_color[stickers, DFace->BL] = Yellow
	get_sticker_color[stickers, DFace->BM] = Yellow
	get_sticker_color[stickers, DFace->BR] = Yellow
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
/*
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
    
	-- This does not terminate!!
	--test expect {
	--	tracesEightStickersPerFace : {traces implies always faceEightStickers} is theorem
	--    tracesEightStickersPerColor : {traces implies always faceEightStickers} is theorem
	--    tracesEightStickersRightPosition : {traces implies always colorStickersRightPosition} is theorem
	--}
	
	--test expect {
	--	eightStickersPerFace : {basics implies faceEightStickers} is theorem
	--    eightStickersPerColor : {basics implies faceEightStickers} is theorem
	--}
	
}
*/

run { traces sticker_based_1_step_scramble }