---
title: "Ethics: first steps"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy
  - ethics
...


## Definition of an ethic

Being given a situation (also named state following the usual terminology in artificial intelligence: see [this Wikipedia page](https://en.wikipedia.org/wiki/Intelligent_agent#Objective_function) for example), an ethic tells if a given action is right or wrong.

--MATH_START--
Throughout this page, let $S$ be the set of states and $A$ the set of actions.

$\mathbf{Definition}$\
An ethic is a function from $S × A$ to $\{⊥ ,⊤\}$, where $⊥$ is the image for actions being unethical and $⊤$ the one for ethical actions. \
Let $E = {\{⊥ ,⊤\}}^{S × A}$ be the set of ethics.
--MATH_END--

[//]: # Rocq (6-10)
[//]: # Lean4 (4-7)


## Restrictiveness

An ethic is more restrictive than an other if all the actions it allows are also allowed by the other.

--MATH_START--
$\mathbf{Definition}$\
An ethic $e_1 \in E$ is said more restrictive than $e_2 \in E$ in a state $s \in S$ if $\forall a \in A, e_1(s, a) = ⊤ \rightarrow e_2(s, a)$. \
And $e_1$ is said strictly more restrictive than $e_2$ in a state $s \in S$ if $e_1$ is more restrictive than $e_2$ and $\exists a \in A, e_1(s, a) = ⊥$ and $e_2(s, a) = ⊤$. \

Obviously, every ethic is more restrictive than itself and is not strictly more restrictive than itself.
--MATH_END--

[//]: # Rocq (12-36)
[//]: # Lean4 (9-14)

A void ethic allows every action. An ethicless person has a void ethic. The void ethic is the least restrictive of all.

--MATH_START--
$\mathbf{Definition}$\
The void ethic is
$$\begin{align*}
    S × A &\to \mathbb \{⊥ ,⊤\}\\
    (s, a) &\mapsto ⊤
\end{align*}$$

Obviously, every ethic is more restrictive than the void ethic.
--MATH_END--

[//]: # Rocq (38-45)
[//]: # Lean4 (23-24)
