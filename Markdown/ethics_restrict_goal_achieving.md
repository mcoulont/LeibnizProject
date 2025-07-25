---
title: "Ethics restrict goal achieving"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy
  - ethics
...


## Presentation

The present article formalizes the fact that, the more you're ethical, the less room to maneuver you have and the less easy it is to reach your goals.

One relies on [this article](https://leibnizproject.com/Articles/ethics_first_steps.html) and [this article](https://leibnizproject.com/Articles/deterministic_stochastic_physics.html).

--MATH_START--
Throughout this page, let $T$ be the time, $S$ the set of states, $A$ the set of actions and $pt$ the physical theory we adopt.

$\mathbf{Definition}$\
Let $SD = T \times S$ be the set of states in a dynamic environment. \
For $sd = (t, s) \in SD$, let $sd_T(sd) = t$ and $sd_S(sd) = s$.

$\mathbf{Definition}$\
Let $E = {\{⊥ ,⊤\}}^{SD × A}$ be the set of ethics ([let $S = SD$ in this article](https://leibnizproject.com/Articles/ethics_first_steps.html)).

$\mathbf{Definition}$\
Let $H = (S \times A)^T$ be the set of histories ([let $S = S \times A$ in this article](https://leibnizproject.com/Articles/deterministic_stochastic_physics.html)). \
For $t \in T$ and $h(t) = (s, a)$, let $h_S(t) = s$ and $h_A(t) = a$.

$\mathbf{Definition}$\
Let $G = {\{⊥ ,⊤\}}^H$ be the set of goals (which are events in [this article with $S = S \times A$](https://leibnizproject.com/Articles/deterministic_stochastic_physics.html)).
--MATH_END--

[//]: # Coq (9-23)


## Ethics can't help to achieve goals

--MATH_START--
$\mathbf{Definition}$\
A $g \in G$ can be achieved if there is a history compatible with the laws of physics in which $g$ happens.

$\mathbf{Definition}$\
An ethic $e \in E$ is followed in a history $h \in H$ at time $t \in T$ if $e((t, h_S(t)), h_A(t)) = ⊤$. \
An ethic $e \in E$ is always followed in a history $h \in H$ if $\forall t \in T, e((t, h_S(t)), h_A(t)) = ⊤$.

$\mathbf{Definition}$\
A $g \in G$ can be achieved ethically with $e \in E$ if there is a history compatible with the laws of physics in which $g$ happens and $e$ is always followed.
--MATH_END--

[//]: # Coq (25-45)

If you can achieve a goal with your ethic, you can without as well.

--MATH_START--
$\mathbf{Lemma}$\
Let $g \in G$ a goal and $e \in E$ an ethic. \
If $g$ can be achieved ethically with $e$, then $g$ can be achieved.

$\mathbf{proof:}$\
Obvious: the history given by the ethical achievement also works for the ethicless achievement. \
■
--MATH_END--

[//]: # Coq (47-56)


## Restrictiveness and goal achieving

An ethic is more restrictive than an other if all the actions it allows are also allowed by the other, whatever the moment and the situation.

--MATH_START--
$\mathbf{Definition}$\
An ethic $e_1 \in E$ is said more restrictive than $e_2 \in E$ in a state $s \in S$ if $\forall t \in T, s \in S, e_1$ is more restrictive than $e_2$ at time $t$ and state $s$ (see [this article](https://leibnizproject.com/Articles/ethics_first_steps.html)). \
And $e_1$ is said strictly more restrictive than $e_2$ if $e_1$ is more restrictive than $e_2$ and $\exists t \in T, s \in S e_1(s, a) = ⊥$ and $e_2(s, a) = ⊤$.
--MATH_END--

[//]: # Coq (58-68)

If you can achieve a goal with your ethic, you can with a less restrictive one as well.

--MATH_START--
$\mathbf{Lemma}$\
Let $g \in G$ a goal and $e_1, e_2 \in E$ ethics such that $e_1$ is more restrictive than $e_2$. \
If $g$ can be achieved ethically with $e_1$, then $g$ can be achieved ethically with $e_2$.

$\mathbf{proof:}$\
As $g$ can be achieved ethically with $e_1$, let $h$ a history compatible with the laws of physics in which $g$ happens and $e_1$ is always followed. \
It suffices to show that $e_2$ is always followed in $h$, which is true because $e_1$ is more restrictive than $e_2$. \
■
--MATH_END--

[//]: # Coq (70-92)

If a goal can be achieved, it can be achieved with a void ethic (that is an ethic which allows everything).

--MATH_START--
$\mathbf{Lemma}$\
Let $g \in G$ a goal which can be achieved. \
Then it can be achieved with the void ethic (see [this article](https://leibnizproject.com/Articles/ethics_first_steps.html)).

$\mathbf{proof:}$\
As $g$ can be achieved, let $h$ a history compatible with the laws of physics in which $g$ happens. \
Then the void ethic is satisfied by every history, so by $h$ in particular. \
■
--MATH_END--

[//]: # Coq (94-111)
