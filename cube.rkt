#lang forge
open "foundations-and-presets.rkt"
-- foundations.rkt contains all the sigs needed for modelling a Rubik's cube
-- and hard-coded rotations and scramble predicates.

--option solver MiniSat
option problem_type temporal
option max_tracelength 5

-- Models the clockwise rotation of a face and updates the stickers relation in 
-- the next state accordingly on all faces.
pred rotate[rf: Face] {
    all f: Face | {
        all p: Position | {
            get_sticker_color[stickers, f->p] = get_sticker_color[stickers', rf.rot[f][p]]
        }
    }
}

-- Models the counter-clockwise rotation of a face and updates the stickers 
-- relation in the next state accordingly on all faces.
pred counter_rotate[rf: Face] {
    all f: Face | {
        all p: Position | {
            get_sticker_color[stickers', f->p] = get_sticker_color[stickers, rf.rot[f][p]]
        }
    }
}

-- A transition predicate that maps positions within a face to their
-- subsequent positions after rotating the face clockwise.
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

-- A transition predicate that specifies that a particular face's sticker configuration
-- does not change over the transition.
pred dontChangeFacePlane[f: Face] {
    -- f.stickers is Position->Color
    f.stickers' = f.stickers
}

-- A predicate that sets up all basic properties of a Rubik's cube, which
-- include transition predicates for rotations, central colors for faces,
-- and opposite faces for each face. This also ensures that each sticker is
-- mapped to exactly one color.
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

-- Each color should have one and only one sticker in each position.
pred colorStickersRightPosition {
    all c : Color | {
        all p : Position | {
            one (stickers.c).p
        }
    }
}

-- A solved state is one where all stickers on the face share the same
-- color as the central sticker on the face.
pred solved {
	all face: Face | {
		face.stickers[Position] = face.center
	}
}

-- A stutter transition predicate to allow Electrum to lasso on the last solved state.
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
	eventually solved
    always(solved iff solved_stutter)
}

-- A predicate describing a trace that begins from a solved state and ends up in an
-- unsolved state reached through a sequence of valid rotations and counter-rotations.
pred scramble {
	basics
	solved
	eventually(always(not solved))
	always(some f: Face | rotate[f] or counter_rotate[f])
    -- NOTE: makes the trace less redundant but might take more time
	--   always(all f: Face | rotate[f] implies not after counter_rotate[f])
	--   always(all f: Face | counter_rotate[f] implies not after rotate[f])
}

-- WARNING:
-- The predicate below requires some changes to our predicates as they are currently defined
-- We should discuss which version we like more next time we meet!
pred move_based_2_step_scramble {
	solved
	rotate[RFace]
	after rotate[UFace]
}

/** PROPERTY VERIFICATION TESTS **/

test expect {
	--eightStickersPerFace : { basics implies (all f : Face | #(f.stickers) = 8) } is theorem

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
    
    solvedImpliesAlwaysSolved : { traces => eventually always solved } is theorem

    // properties to preserve across moves -- 
    
	-- This does not terminate!!
    --tracesEightStickersPerFace : {traces implies always faceEightStickers} is theorem
    --tracesEightStickersRightPosition : {traces implies always colorStickersRightPosition} is theorem
    --alwaysEightStickersForEachColor : {scramble implies always colorEightStickers} is theorem
	
	--test expect {
	--	eightStickersPerFace : {basics implies faceEightStickers} is theorem
	--    eightStickersPerColor : {basics implies faceEightStickers} is theorem
	--}
	
}

run { traces sticker_based_1_step_scramble }