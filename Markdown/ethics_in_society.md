---
title: "Ethics in a society"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - Philosophy
  - Ethics
  - society
...


## Presentation

This page lays the foundations of ethics in a society composed of individuals.

One relies on [this article](https://leibnizproject.com/Articles/ethics_first_steps.html).

--MATH_START--
Throughout this page, let $I$ the finite set of individuals of a society, $S$ be the set of states and $A$ the set of actions.
--MATH_END--

[//]: # Rocq (8-10)


## Profiles and subjective states

An action profile is given by the action of each individual.

--MATH_START--
$\mathbf{Definition}$\
The set $AP$ of action profiles is $A^I$.
--MATH_END--

[//]: # Rocq (12-12)

A subjective state is a situation seen in a specific individual's perspective.

--MATH_START--
$\mathbf{Definition}$\
The set $SubjS$ of subjective states is $S × I$.
--MATH_END--

[//]: # Rocq (14-35)

Permuting two individuals in a state consists in exchanging their roles. For example, if a state is described by "Alice is in jail and Bob is free", permuting Alice and Bob gives "Bob is in jail and Alice is free".

--MATH_START--
$\mathbf{Definition}$\
Let $s$ be a state of $S$ and $\sigma$ a permutation of $S_I$. \
Then $s_\sigma$ is the state obtained by permuting individuals according to $\sigma$ in $s$.

$\mathbf{Definition}$\
Let $(s, i)$ be an individual state and $\sigma$ a permutation of $S_I$. \
Then $(s, i)_\sigma$ is defined as $(s_\sigma, \sigma (i))$.
--MATH_END--

[//]: # Rocq (37-58)

An individual ethic tells for each subjective state if a given action is "right" or "wrong". As a subjective state can put anyone's shoes, so can an individual ethic.

--MATH_START--
$\mathbf{Definition}$\
The set $IE$ of individual ethics is ${\{⊥ ,⊤\}}^{SubjS × A}$.
--MATH_END--

[//]: # Rocq (60-60)

An ethical profile gives the ethic of each individual.

--MATH_START--
$\mathbf{Definition}$\
The set $EP$ of ethical profiles is $IE^I$.

$\mathbf{Definition}$\
Individuals $i, j \in I$ of an ethical profile $ep$ are said to have the same ethic in a subjective state $subjS$ if $\forall a \in A, ep(i)(SubjS, a) = ep(j)(SubjS, a)$.

$\mathbf{Definition}$\
Individuals $i, j \in I$ of an ethical profile $ep$ are said to always have the same ethic if $\forall subjS \in SubjS,$ $i$ and $j$ have the same ethic in $subjS$ .
--MATH_END--

[//]: # Rocq (62-72)
