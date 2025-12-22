---
title: "Occam's razor"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy
  - philosophy of science
...


## Presentation

Here is formalized the deduction of a scientific theory from a record of all what happened.

--MATH_START--
Throughout this page, let $T$ be the set of instants in the unfolding of time. If $t, t' \in T$, $t \le t'$ means that the instant $t$ is before (or simultaneous with) $t'$. \
Let $S$ be the set of states.
--MATH_END--

[//]: # Rocq (9-11)


## Histories and events

A history is a complete description of all what happened through time (successive states). A history until a certain instant is all what happened through time until this instant. A history extends a history until a certain instant if both coincide before that instant.

--MATH_START--
$\mathbf{Definition}$\
The set $H$ of histories is $S^T$. \
The set $H_{t_0}$ of histories until $t_0$ is $S^{\{t \in T | t \le t_0\}}$ (where $t_0 \in T$). \
The set $H_{<t_0}$ of histories before $t_0$ is $S^{\{t \in T | t \lt t_0\}}$ (where $t_0 \in T$).

$\mathbf{Definition}$\
Let $t_0 \in T$, $h \in H$ and ${hu} \in H_{t_0}$. \
$h$ is said to extend ${hu}$ if $\forall t \le t_0, h(t) = {hu}(t)$. \
Let $t_0 \in T$, $h \in H$ and ${hb} \in H_{<t_0}$. \
$h$ is said to extend ${hb}$ if $\forall t \lt t_0, h(t) = {hb}(t)$.
--MATH_END--

[//]: # Rocq (13-57)

As a history contains all the information, it can report which events happened and which didn't.

--MATH_START--
$\mathbf{Definition}$\
The set $E$ of events is ${\{⊥, ⊤\}}^H$, provided $e(h) = ⊤$ when the event $e \in E$ happens in history $h \in H$.
--MATH_END--

[//]: # Rocq (59-65)


## Scientific theories

Looking at the history, you may recognize patterns giving indications about how the environment works. Elaborating a scientific theory amounts to compiling such patterns in a way consistent with the history (and with itself).

--MATH_START--
$\mathbf{Definition}$\
The set $ST$ of scientific theories is ${\{⊥ ,⊤\}}^H$. \
(it is equal to the set of events but its elements are interpreted differently)

$\mathbf{Definition}$\
A history $h \in H$ is said to satisfy a scientific theory $pt \in PT$ if $pt(h) = ⊤$.

$\mathbf{Definition}$\
A history $h_{t_0} \in H_{t_0}$ is said to satisfy a scientific theory $st \in ST$ until $t_0 \in T$ if $\exists h \in H$ extending $h_{t_0}$ such that $st(h) = ⊤$.
--MATH_END--

[//]: # Rocq (67-73)

The more patterns of behavior of the environment you take into account, the more precise is your scientific theory.

--MATH_START--
$\mathbf{Definition}$\
$st_1 \in ST$ is said more precise than $st_2 \in ST$ if $\forall h \in H, st_2(h) = ⊥ \Rightarrow st_1(h) = ⊥$. \
--MATH_END--

[//]: # Rocq (75-76)

## Occam's razor as a way to choose among plausible scientific theories

Considering the scientific theories consistent with the current history, Occam's razor recommends to adopt the simplest one (for example to predict the future). If you don't, your quest to determine the scientific theory describing the laws of the environment as precisely as possible will not take the simplest way either. As an example, if you are given the sequence 0101010101 and must find the following digits, you will probably notice that the sequence alternates between 0 and 1 and predict accordingly, but you may also conjecture that the sequence stops alternating at the 100-th digit. This may be quite an artificial claim though.

--MATH_START--
$\mathbf{Definition}$\
A history $h_{t_0} \in H_{t_0}$ being given, the scientific theory prefered by Occam's razor is the simplest one satisjfying $h_{t_0}$ (whatever the total relation order used to define the simplicity of scientific theories).
--MATH_END--

[//]: # Rocq (78-85)
