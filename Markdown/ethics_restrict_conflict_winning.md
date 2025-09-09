---
title: "Ethics restrict conflict winning"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy
  - ethics
  - society
...


## Presentation

The present article formalizes the fact that, the more you're ethical, the less room to maneuver you have and the less easy it is to win conflicts.

--MATH_START--
Throughout this page, let $T$ be the time, $S$ the set of states, $A$ the set of actions, $I$ the set of individuals in the society and $pt$ the physical theory we adopt.

$\mathbf{Definition}$\
Let $H = (S \times A^I)^T$ be the set of histories ([let $S = S \times A^I$ in this article](https://leibnizproject.com/Articles/deterministic_stochastic_physics.html)). \
For $t \in T, ap \in A^I$ and $h(t) = (s, ap)$, let $h_S(t) = s$ and $h_{AP}(t) = ap$.

$\mathbf{Definition}$\
Let $G = {\{⊥ ,⊤\}}^H$ be the set of goals (which are events in [this article with $S = S \times A^I$](https://leibnizproject.com/Articles/deterministic_stochastic_physics.html)).
--MATH_END--

[//]: # Rocq (14-21)


## Conflicts

A goal profile is given by a goal for each individual.

--MATH_START--
$\mathbf{Definition}$\
The set $GP$ of action profiles is $G^I$.
--MATH_END--

[//]: # Rocq (23-24)

A conflict arises when not everyone can achieve its goal.

--MATH_START--
$\mathbf{Definition}$\
All the goals of $gp \in GP$ can be achieved if $\exists h \in H$ compatible with the laws of physics in which all the individual goals of $gp$ are achieved.
--MATH_END--

[//]: # Rocq (26-30)

Someone wins a conflict when its goal is achieved. There may be more than one individual who achieves its goal.

--MATH_START--
$\mathbf{Definition}$\
An individual $i \in I$ can win a conflict relative to goals $gp \in GP$ if all the goals of $gp$ can't be achieved but $i$'s goal $gp(i)$ can be. \
An individual $i \in I$ can't win a conflict relative to goals $gp \in GP$ if all the goals of $gp$ can't be achieved and $i$'s goal $gp(i)$ can't either.
--MATH_END--

[//]: # Rocq (32-44)


## Following one's ethic

--MATH_START--
$\mathbf{Definition}$\
Everyone follows its ethic in a history $h \in H$ for an ehtical profile $ep$ at time $t$ if $\forall i \in I, ep(i)$ is followed by $i$ in $h$ at time $t$. \
And everyone always follows its ethic in $h$ for $ep$ if $\forall t \in T$ everyone follows its ethic in $h$ for $ep$ at time $t$.
--MATH_END--

[//]: # Rocq (46-76)

--MATH_START--
$\mathbf{Definition}$\
All the goals of $gp \in GP$ can be achieved according to $ep \in EP$ if there is a history $h \in H$ compatible with the laws of physics in which: \
- $\forall i \in I, gp(i)$ happens in $h$ \
- Everyone always follows its ethic in $h$ for $ep$
--MATH_END--

[//]: # Rocq (78-83)

--MATH_START--
$\mathbf{Definition}$\
An individual $i \in I$ can achieve a goal $g \in G$ according to $ep \in EP$ if there is a history $h \in H$ compatible with the laws of physics in which: \
- $gp(i)$ happens in $h$ \
- Everyone always follows its ethic in $h$ for $ep$
--MATH_END--

[//]: # Rocq (85-91)


## Restrictiveness and conflict achieving

Winning a conflict ethically means here winning a conflict while everyone follows its own ethic.

--MATH_START--
$\mathbf{Definition}$\
An individual $i \in I$ can win a conflict relative to goals $gp \in GP$ according to $ep \in EP$ if not all the goals of $gp$ can be achieved according to $ep$ but $i$ can achieve its goal $gp(i)$ according to $ep$. \
And it can't win a conflict relative to goals $gp \in GP$ according to $ep \in EP$ if not all the goals of $gp$ can be achieved according to $ep$ and $i$ can't achieve its goal $gp(i)$ according to $ep$.
--MATH_END--

[//]: # Rocq (93-105)

Winning a conflict ethically means here winning a conflict while everyone follows its own ethic.

--MATH_START--
$\mathbf{Lemma}$\
Let $i \in I$ an individual, $goals \in GP$ a goal profile, $ep \in EP$ an ethical profile and $e$ an ethic such that $ep(i)$ is more restrictive than $e$. \
If $i$ can achieve $gp(i)$ according to $ep$, $i$ can still achieve $gp(i)$ replacing its ethic $ep(i)$ with $e$.

$\mathbf{proof:}$\
Let $h$ a history $h \in H$ compatible with the laws of physics in which: \
- $gp(i)$ happens in $h$ \
- Everyone always follows its ethic in $h$ for $ep$ \
It suffices to show that everyone always follows its ethic in $h$ for $ep_{i/e}$. \
All the individuals but $i$ definitely do so as their ethic is unchanged. \
And so does $i$ because $ep(i)$ is more restrictive than $e$. \
■
--MATH_END--

[//]: # Rocq (107-158)

Winning a conflict ethically means here winning a conflict while everyone follows its own ethic.

--MATH_START--
$\mathbf{Corollary}$\
Let $i \in I$ an individual, $goals \in GP$ a goal profile, $ep \in EP$ an ethical profile and $e$ an ethic such that $ep(i)$ is more restrictive than $e$. \
If $i$ can win a conflict relative to goals $gp \in GP$ according to $ep$, $i$ can still achieve $gp(i)$ replacing its ethic $ep(i)$ with $e$.

$\mathbf{proof:}$\
By definition of winning a conflict, we have $i$ who can achieve its goal $gp(i)$ according to $ep$. Then we just have to apply the previous lemma. \
■
--MATH_END--

[//]: # Rocq (160-180)
