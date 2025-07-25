---
title: "Ethics in a society"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy
  - ethics
  - society
...


## Presentation

This page lays the foundations of ethics in a society composed of individuals.

One relies on [this article](https://leibnizproject.com/Articles/ethics_first_steps.html).

--MATH_START--
Throughout this page, let $I$ the finite set of individuals of a society, $S$ be the set of states and $A$ the set of actions.
--MATH_END--

[//]: # Coq (9-11)


## Profiles and subjective states

An action profile is given by the action of each individual.

--MATH_START--
$\mathbf{Definition}$\
The set $AP$ of action profiles is $A^I$.
--MATH_END--

[//]: # Coq (13-13)

A subjective state is a situation seen in a specific individual's perspective.

--MATH_START--
$\mathbf{Definition}$\
The set $SubjS$ of subjective states is $S × I$.
--MATH_END--

[//]: # Coq (15-36)

An individual ethic tells for each subjective state if a given action is "right" or "wrong". As a subjective state can put anyone's shoes, so can an individual ethic.

--MATH_START--
$\mathbf{Definition}$\
The set $IE$ of individual ethics is ${\{⊥ ,⊤\}}^{SubjS × A}$.
--MATH_END--

[//]: # Coq (38-38)

An ethical profile gives the ethic of each individual.

--MATH_START--
$\mathbf{Definition}$\
The set $EP$ of ethical profiles is $IE^I$.

$\mathbf{Definition}$\
Individuals $i, j \in I$ of an ethical profile $ep$ are said to have the same ethic in a subjective state $subjS$ if $\forall a \in A, ep(i)(SubjS, a) = ep(j)(SubjS, a)$.

$\mathbf{Definition}$\
Individuals $i, j \in I$ of an ethical profile $ep$ are said to always have the same ethic if $\forall subjS \in SubjS,$ $i$ and $j$ have the same ethic in $subjS$ .
--MATH_END--

[//]: # Coq (40-50)


## Replacing an individual ethic

We will be led in the future to replace an individual ethic with another.

--MATH_START--
$\mathbf{Definition}$\
Ethical profiles $ep_1, ep_2 \in EP$ coincide for all individuals but $i \in I$ if $\forall j \neq i \in I, ep_1(j) = ep_2(j).

$\mathbf{Definition}$\
Being given an ethical profile $ep \in EP$, an individual $i \in I$ and an individual ethic $e \in IE$, $ep_{i/e}$ is the ethical profile obtained by replacing the individual ethic $ep(i)$ with $e$. More formally,
$$ep_{i/e}(j) = \begin{cases*}
    e \text{ if } j = i \\
    ep(j) \text{ otherwise}
\end{cases*}$$

It is obvious that ep_{i/e} and $ep$ coincide for all individuals but $i$.
--MATH_END--

[//]: # Coq (52-74)
