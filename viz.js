d3.select(svg).selectAll("*").remove();

const FACE_SIDE = 120;
const STICKER_SIDE = FACE_SIDE / 3;
const MARGIN_LEFT = 30;
const MARGIN_TOP = 30;

const WHITE = '#FFFFFF';
const GREEN = '#00FF00';
const BLUE = '#0000FF';
const RED = '#FF0000';
const ORANGE = '#FFA500';
const YELLOW = '#FFFF00';

const colorMap = {
  "White0": WHITE,
  "Green0": GREEN,
  "Blue0": BLUE,
  "Red0": RED,
  "Orange0": ORANGE,
  "Yellow0": YELLOW
}

// position -> [x/col, y/row]
const positionMap = {
  "TL0": [0, 0],
  "TM0": [1, 0],
  "TR0": [2, 0],
  "ML0": [0, 1],
  "MR0": [2, 1],
  "BL0": [0, 2],
  "BM0": [1, 2],
  "BR0": [2, 2]
}

// (Face, Row::int, Col::int)->Color

function tupleToArray(t) {
  const posn = positionMap[t._atoms[1]._id];
  const face = t._atoms[0]._id;
  return [face, posn[1], posn[0]];
}

let stickerMap = {};
stickers._tuples.map(t => { stickerMap[tupleToArray(t)] = colorMap[t._atoms[2]._id] });
//console.log(UFace.join(center)._tuples[0]._atoms[0]._id)
Face.atoms(true).map(face => { 
  stickerMap[[face._id, 1, 1]] = colorMap[face.join(center)._tuples[0]._atoms[0]._id]
});


const svgSelect = d3.select(svg);

// given top left, stickers for face
// prints rect for each sticker
function printStickersForFace(x, y, face) {
  let topLefts = [];
  let row, col;
  console.log(stickerMap)
  for (row = 0; row < 3; row++) {
    for (col = 0; col < 3; col++) {
       svgSelect
         .append("rect")         // append a rectangle element to the selected element (the svg)
         .attr("x", MARGIN_LEFT + x + col * STICKER_SIDE)          // give the rect an x coordinate
         .attr("y", MARGIN_TOP + y + row * STICKER_SIDE)          // give the rect a y coordinate
         .attr("width", STICKER_SIDE)     // give the rect a width
         .attr("height", STICKER_SIDE)    // give the rect a height
         .style("fill", stickerMap[[face, row, col]])
         .style("stroke-width", 1)
         .style("stroke", '#000000');
    }
  }
}

printStickersForFace(FACE_SIDE, 0, "UFace0")
printStickersForFace(0, FACE_SIDE, "LFace0")
printStickersForFace(FACE_SIDE, FACE_SIDE, "FFace0")
printStickersForFace(FACE_SIDE * 2, FACE_SIDE, "RFace0")
printStickersForFace(FACE_SIDE * 3, FACE_SIDE, "BFace0")
printStickersForFace(FACE_SIDE, FACE_SIDE * 2, "DFace0")