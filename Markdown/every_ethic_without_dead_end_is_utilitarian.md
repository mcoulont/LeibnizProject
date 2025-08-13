---
title: "Every ethic without dead end is utilitarian"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy
  - ethics
  - utility-function
...


## Presentation

It is proved here that every ethic without dead end is utlitarian, in the sense that it maximizes a [utility function](https://en.wikipedia.org/wiki/Utility#Preference).

One relies on [this article](https://leibnizproject.com/Articles/ethics_first_steps.html).

--MATH_START--
Throughout this page, let $S$ be the set of states and $A$ the set of actions.
--MATH_END--

[//]: # Rocq (11-12)
[//]: # Lean4 (10-11)


## Definition of a dead end in an ethic

A dead end is a situation in which the ethic allows no action.

--MATH_START--
$\mathbf{Definition}$\
A dead end in an ethic $e: S × A \to \{⊥ ,⊤\}$ is a state $s \in S$ such that $\forall a \in A, e(s, a) = ⊥$.
--MATH_END--

[//]: # Rocq (14-15)
[//]: # Lean4 (15-16)

An ethic without dead end is an ethic for which no situation is a dead end. Note that this is not an assumption of hope: such a possible action can be "do nothing". It seems possible to assume that every ethic has no dead end (or at least can be slightly modified to remove them, for example adding as ethical action "kill oneself" to situations having none).

--MATH_START--
$\mathbf{Definition}$\
An ethic is without dead end if $\forall s \in S$ $s$ is not a dead end.
--MATH_END--

[//]: # Rocq (17-18)
[//]: # Lean4 (18-19)


## Definition of a utility function

We may have in each situation a preference among all the alternatives of actions.

--MATH_START--
$\mathbf{Definition}$\
A preference order is a total and transitive binary relation. We will in this page denote with $a_1 \ge a_2$ the fact that the alternative $a_1$ is preferable (or equally preferable) to an alternative $a_2$.
--MATH_END--

A utility function gives preferences among all possible alternatives. In our context, you may see this utility function as a measure of the "goodness" of actions.

--MATH_START--
$\mathbf{Definition}$\
A utility function is a function from a set $A$ of alternatives to a set $U$ endowed with a preference order. In our context, the alternatives are the possible actions in each given situation, and a utility function is from $S × A$ to $U$. Strictly speaking, we have a utility function for each state.

Note that the usual utility functions are given with $U$ being the real numbers endowed with the usual $\ge$ operator. We deal with (arguably) the most general definition.
--MATH_END--

[//]: # Rocq (20-21)
[//]: # Lean4 (21-21)


## Definition of an utilitarian ethic

An ethic is said to maximize a utility function if for each situation it imposes the action with the maximum goodness. There may be more than one such action.

--MATH_START--
$\mathbf{Definition}$\
An ethic $e$ maximizes a utility function $u$ if
$$\forall s \in S,\ \forall a \in A,\ e(s, a)=⊤ \iff \forall a' \in A,\ u(a) \ge u(a')$$
--MATH_END--

[//]: # Rocq (23-36)
[//]: # Lean4 (23-36)

An ethic is said to be utilitarian if it maximizes a utility function.

--MATH_START--
$\mathbf{Definition}$\
An ethic $e$ is utilitarian if there is a utility function $u$ such that $e$ maximizes $u$.
--MATH_END--

[//]: # Rocq (38-39)
[//]: # Lean4 (38-40)


## Proving that every ethic (without dead end) is utilitarian

An ethic being given, we can for each situation assign the value $1$ to the approved action(s) and $0$ to the disapproved ones.

--MATH_START--
$\mathbf{Definition}$\
An ethic $e$ being given, its associated utility is the following function:
$$\begin{align*}
    S × A &\to \mathbb R\\
    (s, a) &\mapsto \begin{cases*}
        1 \text{ if } e(s, a) = ⊤ \\
        0 \text{ if } e(s, a) = ⊥
    \end{cases*}
\end{align*}$$
--MATH_END--

[//]: # Rocq (41-43)
[//]: # Lean4 (42-52)

If the ethic has no dead end, this gives a utility function it maximizes.

--MATH_START--
$\mathbf{Proposition}$\ 
Every ethic without dead end is utilitarian.

$\mathbf{proof:}$\
Let $e$ be an ethic without dead end. \
By definition of utilitarian, it suffices to show that $e$ maximizes its associated utility (which we note $au$), that is: \
$$\forall s \in S,\ \forall a \in A,\ e(s, a)=⊤ \iff \forall a' \in A,\ au(a) \ge au(a')$$
Let $s \in S$ and $a \in A$. \
As $e$ has no dead end, by definition of the associated utility, there is an action whose image by $au$ is $1$, which is thus the maximum value of $au$ (because the other possible value is $0$), that is: \
$$\forall a' \in A,\ au(a) \ge au(a') \iff au(a) = 1$$
And $e(s, a)=⊤ \iff au(a) = 1$ results from the definition of the associated utility \
■
--MATH_END--

[//]: # Rocq (45-70)
[//]: # Lean4 (54-98)
