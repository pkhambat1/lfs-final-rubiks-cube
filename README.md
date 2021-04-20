# README
## Overview
This project involves modeling a 3x3 Rubik’s cube in Electrum. In doing so, we aimed to set up the framework to obtain states for solved Rubik’s cubes, valid scrambles (i.e. states reachable in a cube), and using temporal logic, obtain lassos that display the process of solving a Rubik’s cube, i.e. starting from an unsolved state and concluding on a solved one. We also developed a JavaScript visualizer for the models we obtained, which outputs SVG images given traces outputs on Sterling. An example of a scramble and the solved state obtained from it could be:
![Image of scrambled and solved cube](https://i.imgur.com/ysTKLcg.png)

## Building, Running, and Visualization
Building and running the project from inside the project folder merely involves entering `racket cube.rkt` in the terminal, which should open up a Sterling window for the given instance. While the initial graph output might seem complex and rather unintelligible, this could be made clearer by moving into the `</> Script` tab, choosing the `viz.js` file, selecting the SVG mode, and clicking on the `execute` button. Stepping through the trace will cause the visualisation to change as well.
## Goals: What Worked and What Didn’t
This project turned out to be significantly more challenging than we had anticipated. Given the sheer number of possibilities that are generated as moves on Rubik’s cubes are compounded, it took prohibitively long to run our model with a scramble 20 moves away from the solved state (>20 minutes), and this made development harder as well, since small changes often tended to break our model in ways that would make it take longer than it should. As a result, we weren’t able to meet our reach goals of encoding algorithms for solving cubes and visualizing their steps on Sterling, even though we did successfully reach our target goals, by managing to model transitions, cubes, and solving cubes upto ~10 steps away from a solved state in a reasonable amount of time. 

The large set of possibilities for the project also led to uncertainty about whether adding certain constraints sped up the solving process or slowed it down. There were tradeoffs between fewer pointless or repeated moves in regular traces making solving theoretically simpler, and the extra time required to process those optimizations themselves. Since we were getting mixed results, we have included solvers both with and without optimizations in the cube.rkt file.
## Design Choices
### Desired Degree of Abstraction and Extensibility
One of the first decisions we were faced with was a meta decision about how extensible and abstract we wanted our model to be. We instantly recognized that extensible and specialized (for 3x3 Rubik’s cubes with fixed colors) would take us in significantly different directions by affecting questions of face-color correlation, encoding transitions, etc. In thinking about the sheer size of the problem space, however, we realized we would need to minimize the number of ambiguities in the model in order to get the results we would need in a reasonable amount of time. For example, general transition predicates preserving face orientations would need a lot of code to model in a general way, and it would still likely be slower than hard-coded transitions for a 3x3 cube. Therefore, we decided to air on the side of specificity with most of our design decisions, even if that meant this would not be easily generalizable to other dimensions of cubes, other colors, etc.
### States in Forge versus Time Steps in Electrum
Since we were essentially trying to model state transitions for Rubik’s cubes, we could either model traces in Forge or in Electrum. In discussing this with Ben Ryjikov, our mentor TA, we learned that the former could potentially work out better in terms of speed. Moreover, at the time, we didn’t know how to create JavaScript visualizations for Electrum. However, several of the properties we wanted to ensure required temporal operators like `always` and `eventually`, which were much simpler to work with in Electrum. This, the increased simplicity of representation, paired with how it reduced our test-writing time, led us to pick Electrum over regular Forge for this project.
## Abstraction Choices
### General Cube Representation
The two main cube representations we considered were sticker-by-sticker representations versus piece-by-piece representations. The former would involve a Face → Position mapping for individual stickers on the cube, whereas the latter would represent each edge and corner piece separately and transitions would consist of newer rotation predicates specializing on such a distribution. In order to maintain simplicity within our predicates, we tried our best to avoid this representation and stick with one that is easier to conceptualize when reading our model’s code. 

 * Piece-based
     * Good: valid piece checking is easier (no all-red corner, no one-color edge)
     * Bad: keeping track of positions with respect to each other -- harder
 * Sticker-based:
     * Good: Face x Position representation for individual stickers
     * Questions: keeping track of where faces are relative to each other?
     * Bad: lots of combinations for face definitions?

→ Sticker/Face-wise representation was chosen.

We also briefly considered modeling in accordance with the group theory of Rubik’s cubes, but none of us had the necessary background knowledge to confidently create predicates for that, even though the idea was intriguing.
### Frames of Reference and Invariants
In order to maintain uniform notions of order and orientation within our cube model, it was necessary for us to decide on a frame of reference for the cube. This would also be helpful for keeping track of transitions in our visualization. For this purpose, we had the central square of each face correspond to a fixed color, and decided to never allow directly moving middle rows / columns in our transitions. This does not limit the scrambles we can represent, as the center pieces are always oriented in the same way relative to each other (rotating a middle layer is equivalent to rotating the two outside layers in the opposite direction).

On the other hand, keeping track of permutations was a much less intuitive process. We assigned 8 position sigs corresponding to each sticker on a face of the cube (excluding the central one, as we have constrained those to never move), and these illustrated different permutations. A graphical representation of these positions is linked here:

![Image of faces of cube and their and orientations](https://i.imgur.com/3v0BfTE.png)
### Rotations and Orientation
We spent a significant amount of time trying to figure out ways to encode rotations that did not involve hard-coding most transitions, but this turned out to be very challenging due to the fact that position orientations (eg. the arrangement of TL, …, BR) have unique arrangements on different faces. Rotating the front face, for example, causes a different transformation mapping of positions on the front face than it does on the right face. In our search for more general ways of doing this, we attempted to infer these transformations from the faces adjacent to each face, earlier stored by fields called `.toup`, `.todown`, `.toleft`, etc, but we realized that the number of cases we would have to handle individually would be nearly equivalent to hardcoding transitions and would probably take more time to solve. We considered a few other options, but for each case, we concluded that hard-coding transitions would be simpler and more quicker to implement.
### Organizing Optimizations
In addition to the barebones predicates required to model cubes, scrambles, and transitions, we realized that we could potentially trim down on the computational space that the solver needs to cover by preventing different redundant sequences of moves. We provide these in an `less_naive_solver` predicate, which can be run alongside regular traces. These “optimizations” actually slowed down the solver, however, so we recommend only running it on simpler scrambles.
## Testing Properties
Some properties we envisioned testing needed higher-order quantification, like testing that each available color has 8 stickers throughout every step of a trace. Similarly, we thought about testing to prove God’s number (i.e. any scramble of a Rubik’s cube can be solved in at most 26 moves given our metrics, upon disallowing middle row/column movements), but that would also require higher-order quantification and would also be computationally infeasible. Upon adjusting for order and computational feasibility, we tested for the following properties:
 - Each face always has eight stickers
 - Repeating a move four times is equivalent to an identity transformation
 - Making a move and the counter of that move gives the same cube.
 - Rotating a face has no effect on the opposite face
 - The stickers on a face rotate according to a fixed transformation
 - <ADD MORE>
## Division of Labor
Much of the work for this project was conceptual, and as a consequence, most of the work was done on Zoom calls with most if not all team members present. We followed a driver-navigator model for this, and each member drove at one point or the other. Within our team, Alex was the most familiar with the techniques and mechanics of Rubik’s cubes, so his intuitions helped drive the transition predicates in particular. Jiahua and Swetabh’s familiarity was critical to the creation of our visualization script. Pezanne came up with good ideas for abstractions and also made us realize that many of our assumptions were unreasonable.
