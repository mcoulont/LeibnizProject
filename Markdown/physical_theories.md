---
title: "Physical theories"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - Philosophy
  - Philosophy of science
  - physics
...


## Presentation

Here is proposed a formalization of the concept of physical theory, and what it is to be deterministic.

--MATH_START--
Throughout this page, let $T$ be the set of instants in the unfolding of time. If $t, t' \in T$, $t \le t'$ means that the instant $t$ is before (or simultaneous with) $t'$. \
Let $S$ be the set of states.
--MATH_END--

[//]: # Rocq (7-10)


## Physical theories

A physical theory comes down to the ability to determine whether a given history is physically possible or not (being given this ability, we may describe its behaviour in physical laws).

--MATH_START--
$\mathbf{Definition}$\
The set $PT$ of physical theories is ${\{⊥ ,⊤\}}^H$. \
(it is equal to the set of events but its elements are interpreted differently)

$\mathbf{Definition}$\
A history $h \in H$ is said to satisfy a physical theory $pt \in PT$ if $pt(h) = ⊤$
--MATH_END--

[//]: # Rocq (12-12)

## Determinism

A physical theory is deterministic when a given state at a given instant determines all the other states after that instant: if we know everything at the present moment, we can (in theory) describe all that's going to happen. For example, classical and relativistic mechanics are deterministic. See for example [the page 12 of this article](https://philsci-archive.pitt.edu/11437/1/Muller-Placek-Defining-Determinism.pdf).

--MATH_START--
$\mathbf{Definition}$\
A physical theory $pt \in PT$ is said deterministic if $\forall h_1, h_2 \in H$ which satisfy $pt$ and such that $h_1(t_0) = h_2(t_0)$ for a given $t_0 \in T$, then $\forall t \gt t_0, h_1(t) = h_2(t)$.
--MATH_END--

[//]: # Rocq (14-30)

## Time-translation symmetry

A physical theory is said to respect time-translation symmetry if shifting the time by a given amount does not change satisfiability.

--MATH_START--
$\mathbf{Definition}$\
Let $h \in H$ and $\delta$ an amount of time. \
$h_\delta$ is defined as the history $t \mapsto h(t + \delta)$.

$\mathbf{Definition}$\
$pt \in PT$ is said to respect time-translation symmetry if $\forall \delta$ amount of time and $\forall h \in H$, $h$ satisfies $pt$ if and only if $h_\delta$ satisfies $pt$.
--MATH_END--

[//]: # Rocq (32-38)
