#lang forge
option problem_type temporal

abstract sig Color {}
one sig White, Green, Orange, Red, Blue, Yellow extends Color {}

abstract sig Position {}
one sig TL, TM, TR, ML, MR, BL, BM, BR extends Position {}

abstract sig Face {
	center: one Color,
	opposite: one Face,
	var stickers: set Position->Color,
	rot: set Face->Position->Face->Position
}

one sig UFace, FFace, LFace, RFace, BFace, DFace extends Face {}

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