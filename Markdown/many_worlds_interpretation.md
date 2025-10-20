---
title: "The many-worlds interpretation"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy of science
  - physics
...


## Presentation

Here is proposed a formalization of the concept of physical theory, and what it is to be deterministic.

--MATH_START--
Throughout this page, let $T$ be the set of instants in the unfolding of time. If $t, t' \in T$, $t \le t'$ means that the instant $t$ is before (or simultaneous with) $t'$. \
Let $S$ be the set of states.
--MATH_END--


## Histories and events

A history is a complete description of all what happened through time (successive states). A history until a certain instant is all what happened through time until this instant. A history extends a history until a certain instant if both coincide before that instant.

--MATH_START--
$\mathbf{Definition}$\
The set $H$ of histories is $S^T$. \
The set $H_{t_0}$ of histories until $t_0$ is $S^{\{t \in T | t \le t_0\}}$ (where $t_0 \in T$). \
The set $H_{<t_0}$ of histories before $t_0$ is $S^{\{t \in T | t \lt t_0\}}$ (where $t_0 \in T$).

$\mathbf{Definition}$\
Let $t_0 \in T$, $h \in H$ and ${hu} \in H_{t_0}$. \
$h$ is said to extend ${hu}$ if $\forall t \le t_0, h(t) = {hu}(t)$.
--MATH_END--

[//]: # Rocq (12-22)

As a history contains all the information, it can report which events happened and which didn't.

--MATH_START--
$\mathbf{Definition}$\
The set $E$ of events is ${\{⊥, ⊤\}}^H$, provided $e(h) = ⊤$ when the event $e \in E$ happens in history $h \in H$.
--MATH_END--

[//]: # Rocq (24-27)


## Physical theories

A physical theory comes down to the ability to determine whether a given history is physically possible or not (being given this ability, we may describe its behaviour in physical laws).

--MATH_START--
$\mathbf{Definition}$\
The set $PT$ of physical theories is ${\{⊥ ,⊤\}}^H$. \
(it is equal to the set of events but its elements are interpreted differently)

$\mathbf{Definition}$\
A history $h \in H$ is said to satisfy a physical theory $pt \in PT$ if $pt(h) = ⊤$
--MATH_END--

[//]: # Rocq (29-31)

An event is possible if there exists a physically possible history in which it happens.

--MATH_START--
$\mathbf{Definition}$\
An event $e \in E$ is said possible in a physical theory $pt \in PT$ if $\exists h \in H$ which satisfies $pt$ such that $e(h)=⊤$.
--MATH_END--

[//]: # Rocq (33-34)

## Determinism

A physical theory is deterministic when a given state at a given instant determines all the other states after that instant: if we know everything at the present moment, we can describe all that's going to happen. For example, classical and relativistic mechanics are deterministic. See for example [the page 12 of this article](https://philsci-archive.pitt.edu/11437/1/Muller-Placek-Defining-Determinism.pdf).

--MATH_START--
$\mathbf{Definition}$\
A physical theory $pt \in PT$ is said deterministic if $\forall h_1, h_2 \in H$ which satisfy $pt$ and such that $h_1(t_0) = h_2(t_0)$ for a given $t_0 \in T$, then $\forall t \gt t_0, h_1(t) = h_2(t)$.
--MATH_END--

[//]: # Rocq (36-52)
