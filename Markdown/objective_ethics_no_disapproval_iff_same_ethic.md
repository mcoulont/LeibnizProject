---
title: "If every individual ethic is objective, no possible disapproval iff everyone has the same ethic"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy
  - ethics
  - society
...


## Presentation

In a society composed of individuals, each of them being [objective](https://en.wikipedia.org/wiki/Subjectivity_and_objectivity_(philosophy)) in his ethic, it is proved here that it's not possible that an individual disapproves an action by another individual if and only if all the individuals have the same ethic.

One relies on [this article](https://leibnizproject.com/Articles/ethics_first_steps.html).

--MATH_START--
Throughout this page, let $I$ the finite set of individuals of a society, $S$ be the set of states and $A$ the set of actions.
--MATH_END--

[//]: # Coq (2-10)


## Definition of a subjective state

A subjective state is a situation seen in a specific individual's perspective.

--MATH_START--
$\mathbf{Definition}$\
A subjective state is a pair $(s, i)$, where $s \in S$, $i \in I$.
--MATH_END--

[//]: # Coq (12-33)


## Individual ethics in society

An individual ethic tells for each subjective state if a given action is "right" or "wrong". As a subjective state can put anyone's shoes, so can an individual ethic.

--MATH_START--
$\mathbf{Definition}$\
An individual ethic is a function which at each subjective state and action associates $⊥$ if the action is considered ethically right and $⊤$ if it's considered wrong.
--MATH_END--

[//]: # Coq (35-35)

An individual profile gives the ethic of each individual.

--MATH_START--
$\mathbf{Definition}$\
An ethical profile is a function which at each individual $i \in I$ associates an individual ethic.
--MATH_END--

[//]: # Coq (36-46)


## Objectivity

Permuting two individuals in a state consists in exchanging their roles. For example, if a state is described by "Alice is in jail and Bob is free", permuting Alice and Bob gives "Bob is in jail and Alice is free".

--MATH_START--
$\mathbf{Definition}$\
Let $s$ be a state of $S$ and $\sigma$ a permutation of $S_I$.
Then $s_\sigma$ is the state obtained by permuting individuals according to $\sigma$ in $s$.

$\mathbf{Definition}$\
Let $(s, i)$ be an individual state and $\sigma$ a permutation of $S_I$.
Then $(s, i)_\sigma$ is defined as $(s_\sigma, \sigma (i))$.
--MATH_END--

[//]: # Coq (48-75)

An individual ethic is said objective if it does not depend on persons (only on states). To be more concrete, if the state is "Alice is in jail and Bob is free" and if one's ethic specifies that someone in jail should be able to have a job, this ethical rule must apply whether it's Alice or Bob who's in jail. An objective ethic requires in some way an equality of rights, but an objective ethic can include something like "the richest one can do whatever (s)he wants", provided it applies whoever is the richest one.

--MATH_START--
$\mathbf{Definition}$\
An individual ethic $e$ is said objective if
$$\forall state \in S, i \in I, \sigma \in S_I, a \in A, e((s, i)_\sigma, a) = e((s, i), a)$$
--MATH_END--

[//]: # Coq (77-86)


## Disapproval

An individual $i$ may disapprove another individual $j$ if there's an action which:
- $j$'s ethic allows him in his position
- $i$'s ethic wouldn't allow him if he was in $j$'s position

--MATH_START--
$\mathbf{Definition}$\
Let $i, j$ be two individuals, with respective ethics $e_i, e_j$.
$i$ may disapprove $j$ in state $s$ if
$$\exists a \in A, e_j((s, j), a) = ⊤ \text{ and } e_j((s, i), a) = ⊥$$
--MATH_END--

[//]: # Coq (88-103)


## Disapproval with objective individual ethics

Two individuals having the same ethic may not disapprove one another.

--MATH_START--
$\mathbf{Lemma}$\
If two individual ethics $e_i, e_j$ are identical in a state $s$ seen by $j$, then $i$ may not disapprove $j$ in this state.

$\mathbf{proof:}$\
Let $a$ be an action. \
As $e_i((s, j), a) = e_j((s, j), a)$, it's not possible that $e_j((s, j), a) = ⊤$ and $e_i((s, j), a) = ⊥$, which prevents a disapproval. \
■
--MATH_END--

[//]: # Coq (105-115)

If two individuals are objective and may not disapprove with one another, then they have the same ethic.

--MATH_START--
$\mathbf{Proposition}$\
Let $i, j$ be two individuals with respective objective ethics $e_i, e_j$.
If $i$ and $j$ may disapprove one another in no state, then $e_i = e_j$.

$\mathbf{proof:}$\
Let's suppose by contradiction that $e_i \neq e_j$. \
Then there are a subjective states $(s, k)$ and an action $a$ such that $e_i((s, k), a) \neq e_j((s, k), a)$. \
Let's suppose for example that $e_i((s, k), a) = ⊤$ and $e_j((s, k), a) = ⊥$ (the other case $e_i((s, k), a) = ⊥$ and $e_j((s, k), a) = ⊤$ is analogous). \
Let's denote $(i, k)$ the permutation swapping $j$ and $k$, and letting the other individuals unchanged. \
By objectivity of $i$, $e_i((s, k), a)_{(i, k)} = e_i((s, k), a)$. \
And by definition of permutations on states, $e_i((s, k), a)_{(i, k)} = e_i((s_{(i, k)}, (i, k)(k)), a) = e_i((s_{(i, k)}, i), a)$ (this remains true if $k$ equals $i$ or $j$, provided that $(i,i) = id$). \
Which gives us 
$$\begin{equation}
  \tag{1}
  e_i((s_{(i, k)}, i), a) = ⊤
\end{equation}$$
On $e_j$'s side, by objectivity of $j$, $e_j((s, k), a)_{(i, k)} = e_j((s, k), a)$. \
And by definition of permutations on states, $e_j((s, k), a)_{(i, k)} = e_j((s_{(i, k)}, (i, k)(k)), a) = e_j((s_{(i, k)}, i), a)$. \
Which gives us $e_j((s_{(i, k)}, i), a) = ⊥$. \
Together with $(1)$, this gives that $j$ may disapprove $i$, which is in contradiction with a hypothesis. \
■
--MATH_END--

[//]: # Coq (117-204)

Overall, in a society where everyone is objective in his ethic, there is no possible disapproval if and only everyone has the same ethic.

--MATH_START--
$\mathbf{Corollary}$\
If $\forall i \in I,$ $e_i$ is objective,
$$\forall i,j \in I, i \text{ may not disapprove } j \iff \forall i,j \in I, e_i = e_j$$

$\mathbf{proof:}$\
$\Rightarrow$ is a straightforward consequence of the previous proposition. \
$\Leftarrow$ is obtained by generalizing the last lemma on all individuals and states. \
■
--MATH_END--

[//]: # Coq (206-233)
