---
title: "A definition of corruption"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - Politics
...


## Presentation

Here is formalized the concept of corruption of a group of (potentially only one) policymakers by a group of (potentially only one) individuals in a society.

--MATH_START--
Throughout this page, let: \
- $I$ be the set of individuals in a society \
- $S$ be the set of possible states of the society \
- $CP \subseteq S^S$ be a set of choosable policies for the society \
- $bc$ be the function which, given a group of policymakers and a society state, returns the chosen policy if the policymakers are honest and want to choose what's best for the society \
- $ac$ be the function which, given a group of policymakers and a society state, returns the actual chosen policy \
- $\succ_i$ be individual $i$'s preference order over $S$
--MATH_END--

[//]: # Lean4 (6-11)


## Upstanding policymakers

The upstanding choice by policymakers is just the choice they make if they care only about social welfare. A group of policy makers is upstanding if it makes the upstanding choice whatever the situation.

--MATH_START--
$\mathbf{Definition}$\
Let $D \subseteq I$ be a set of deciders for a policy and $s \in S$ be a societal state. \
The upstanding choice is defined as $bc(D)(s)$.

$\mathbf{Definition}$\
A set of deciders $D \subseteq I$ is said upstanding if $\forall s \in S, bc(D)(s) = ac(D)(s)$.
--MATH_END--

[//]: # Lean4 (13-20)


## Decisions driven by self-interest

The most straightforward way for the policymakers not to drive their social decision by political conviction is self-interest: they don't choose for the collective welfare but for their personal one. This does not need to be done by the entirety of policymakers: a subset of them may be sufficient (typically one-half in democracy).

--MATH_START--
$\mathbf{Definition}$\
Let $D \subseteq I$ be a set of deciders and $D' \subseteq D$. \
Let $s \in S$ be a societal state and $c \in S^S$ be a social choice. \
$D'$ is said to be able to decide $c$ unilaterally in $s$ if $ac(D')(s) = c \Rightarrow ac(D)(s) = c$. \
If moreover $ac(D')(s) = c$, $D'$ is said to decide unilaterally.

$\mathbf{Definition}$\
Let $D \subseteq I$ be a set of deciders and $D' \subseteq D$. \
Let $s \in S$ be a societal state and $c \in S^S$ a social choice. \
Self-interest is said to be able to prevail if: \
- $D'$ is able to decide $c$ unilaterally \
- $\forall i \in D', c(s) \succ_i bc(D')(s)$ \
If moreover $ac(D')(s) = c$, self-interest is said to prevail.
--MATH_END--

[//]: # Lean4 (22-50)


## Defining corruption

There is corruption if a group of individuals (corrupters) performs an action which makes the policymakers change their decision in a way which favors the corrupters. This could be done by giving money, blackmailing, manipulating...

--MATH_START--
$\mathbf{Definition}$\
Let $D \subseteq I$ be a set of deciders for a policy and $s \in S$ be a societal state. \
A non-empty set $C \subseteq I$ has an opportunity of corruption with an action $a$ if $\forall i \in C, ac(D)(a(C)(s)) \succ_i ac(D)(s)(s)$.

$\mathbf{Definition}$\
Let $D \subseteq I$ be a set of deciders for a policy and $s \in S$ be a societal state. \
$s$ is said prone to corruption with deciders $D$ if $\exists C \subseteq I$ non-empty which has an opportunity of corruption with some action $a$.
--MATH_END--

[//]: # Lean4 (52-64)
