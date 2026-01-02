# Proof of Dijkstra's algorithm in Rocq

This repository contains a proof of Dijkstra's algorithm using the Rocq prover.

A few comments:

## about the invariant

in the proof the invariant we use basically says
- for all vertex v not in the priority queue, either dist[v] is infinite and there is no path from src to v, or dist[v] is the optimal distance from src to v **and there is a path from src to v having that weight and not going through any vertex still in the queue** (we call restricted a path only encountering node not in the queue)
- for all vertex v in the priority queue, either dist[v] is infinite and there is no restricted path from src to v, or dist[v] is the optimal distance for restricted path from src to v
- (we also have a third condition involving length dist, but this is not fundamental: it is just linked and forced by our implementation)

note that:
- for node not in the queue, the idea is that we have a restricted path that is optimal among all paths
- for node in the queue, the idea is that we have a restricted path that is optimal among all restricted paths

also note that most sources I found use a weaker invariant that I think is incorrect (they forgot the bold part of the invariant written above). Indeed, our bold condition (namely, forcing node not in the queue to have an optimal path restricted to node not in the queue) is important as shows the following example :

let us consider the following graph: a line graph with four vertices and only weigth 0

s -0> v -0> v0 -0> u

let us consider this state of memory at the beginning of one loop:
```
d=[s:0, v:0, v0:0, u:inf]
queue = [v, u]
```
the "weak and wrong invariant" is verified:
- for s and v0: optimal distances
- for v and u: we have the optimal restricted distances: only v has a restricted path.

---

v is popped from the queue

v has one neighbour and can't improve its distance: dist is not changed
```
d=[s:0, v:0, v0:0, u:inf]
queue=[u]
```

now the "weak and wrong invariant" is no longer verified (we have a restricted path for u0, yet dist[u] = inf

---

and if we keep going: u is popped, u has ne neighbour, so dist is unchanged

and now the queue is empty so the algorithm returns
```
d=[s:0, v:0, v0:0, u:inf]
```

which is obviously wrong, yet the algorithm started with a state memory verifying the "weak and wrong invariant".

## about efficiency

In my implementation of Dijkstra, I use a simple list for the priority queue, and actually, I kind of used lists everywhere, which is very inefficient.

My goal here was to give a constructive proof of correctness of the algorithm, not to speak about complexity.

I know the complexity of my implementation is just horrible, but anyway, I would not have written a code in Rocq if I wanted to run it someday, or if I was seeking any kind of efficiency.







