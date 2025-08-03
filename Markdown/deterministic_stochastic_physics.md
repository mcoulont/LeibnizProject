---
title: "Deterministic and stochastic physical theories"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - physics
...


## Presentation

Until now, time was not taken into account: we were in a given state at a certain instant and had a range of actions at our disposal, to do in the instant.

Not only time is modeled here, but the concept of physical theories.

--MATH_START--
Throughout this page, let $T$ be the set of instants in the unfolding of time. If $t, t' \in T$, $t \le t'$ means that the instant $t$ is before (or simultaneous with) $t'$. \
Let $S$ be the set of states.
--MATH_END--

[//]: # Rocq (8-12)


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

[//]: # Rocq (15-25)

As a history contains all the information, it can report which events happened and which didn't.

--MATH_START--
$\mathbf{Definition}$\
The set $E$ of events is ${\{⊥, ⊤\}}^H$, provided $e(h) = ⊤$ when the event $e \in E$ happens in history $h \in H$.
--MATH_END--

[//]: # Rocq (27-30)


## Physical theories

A physical theory comes to down to the ability to determine whether a given history is physically possible or not (being given this ability, we may describe its behaviour in physical laws).

--MATH_START--
$\mathbf{Definition}$\
The set $PT$ of physical theories is ${\{⊥ ,⊤\}}^H$. \
(it is equal to the set of events but its elements are interpreted differently)

$\mathbf{Definition}$\
A history $h \in H$ is said to satisfy a physical theory $pt \in PT$ if $pt(h) = ⊤$
--MATH_END--

[//]: # Rocq (32-34)

An event is possible if there exists a physically possible history in which it happens.

--MATH_START--
$\mathbf{Definition}$\
An event $e \in E$ is said possible in a physical theory $pt \in PT$ if $\exists h \in H$ which satisfies $pt$ such that $e(h)=⊤$.
--MATH_END--

[//]: # Rocq (36-37)

A physical theory is deterministic when a given state at a given instant determines all the other states after that instant: if we know everything at the present moment, we can describe all that's going to happen. For example, classical and relativistic mechanics are deterministic.

--MATH_START--
$\mathbf{Definition}$\
A physical theory $pt \in PT$ is said deterministic if $\forall h_1, h_2 \in H$ which satisfy $pt$ and such that $h_1(t_0) = h_2(t_0)$ for a given $t_0 \in T$, then $\forall t \ge t_0, h_1(t) = h_2(t)$.
--MATH_END--

[//]: # Rocq (39-46)
