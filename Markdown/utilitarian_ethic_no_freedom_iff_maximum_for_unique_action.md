---
title: "For an utilitarian ethic, no freedom iff maximum utility reached for a unique action"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy
  - ethics
  - utility-function
...


## Presentation

An ethic being said to leave no freedom when it allows a unique action, it is proved here that for every utlitarian ethic (that is every ethic without dead end according to [this article](https://leibnizproject.com/Articles/every_ethic_without_dead_end_is_utilitarian.html), there is no freedom if and only if the maximum utility is reached for a unique action.

The context is the same as in [this article](https://leibnizproject.com/Articles/every_ethic_without_dead_end_is_utilitarian.html).

--MATH_START--
Throughout this page, let $S$ be the set of states and $A$ the set of actions.
--MATH_END--

[//]: # Coq (2-11)
[//]: # Lean4 (8-9)


## Definition of freedom left by an ethic

In a given situation, an ethic is said to leave no freedom if allows a unique action.

--MATH_START--
$\mathbf{Definition}$\
Let $s$ in $S$. An ethic $e$ leaves no freedom in state $s$ if
$$\exists! a, e(s, a) = ⊤$$
--MATH_END--

[//]: # Coq (13-14)
[//]: # Lean4 (14-15)

An ethic is said to never leave freedom if it leaves no freedom in every situation.

--MATH_START--
$\mathbf{Definition}$\
An ethic $e$ never leaves freedom if $\forall s \in S$, $e$ leaves no freedom in $s$.
--MATH_END--

[//]: # Coq (16-17)
[//]: # Lean4 (17-18)


## Relationship between freedom and dead ends

In a given situation, if an ethic leaves no freedom, then it still allows an action and therefore we are not in a dead end.

--MATH_START--
$\mathbf{Lemma}$\
If an ethic $e$ leaves no freedom in a state $s$, then $s$ is not a dead end for $e$.

$\mathbf{proof:}$\
Let $e$ be an ethic and $s$ be a state in which $e$ leaves no freedom. \
By definition, there is a unique action $a$ allowed by $e$ in $s$. \
Then this action $a$ is allowed by $e$ in $s$, which means that $s$ is not a dead end \
■
--MATH_END--

[//]: # Coq (19-27)
[//]: # Lean4 (20-31)

Therefore, if an ethic never leaves freedom, then it is without dead end.

--MATH_START--
$\mathbf{Corollary}$\
An ethic which never leaves freedom is without dead end.

$\mathbf{proof:}$\
Let $e$ be an ethic which never leaves freedom. \
By definition, $\forall s \in S$, $e$ leaves no freedom in $s$. \
By the previous lemma, $\forall s \in S$, $s$ is not a dead end for $e$, which means it is without dead end. \
■
--MATH_END--

[//]: # Coq (29-34)
[//]: # Lean4 (33-40)


## Maximum utility reached for a unique action

--MATH_START--
$\mathbf{Definition}$\
An utilitarian ethic $e$ (endowed with a utility function called $uf$) is said to have a unique action $a$ maximizing its utility if
$$\begin{cases*}
  \forall a' \in A, uf(s, a') \le uf(s, a) \text{ (where $\le$ designating the prefereence order associated with the utility function)} \\
  \forall a' \in A, uf(s, a') = uf(s, a) \implies a' = a
\end{cases*}$$
--MATH_END--

[//]: # Coq (36-38)
[//]: # Lean4 (42-44)

--MATH_START--
$\mathbf{Definition}$\
An utilitarian ethic $e$ is said to always have a unique action maximizing its utility if $\forall s \in S$, $e$ has a unique maximum action maximizing its utility
--MATH_END--

[//]: # Coq (40-42)
[//]: # Lean4 (46-48)


## An utilitarian ethic has a unique function maximizing its utility if and only if it leaves no freedom

--MATH_START--
$\mathbf{Proposition}$\
A utilitarian ethic $e$ has a unique action maximizing its utility in a state $s$ iff it leaves no freedom in $s$.

$\mathbf{proof:}$\
Let $e$ be a utilitarian ethic, $uf$ its utility function and $s$ a state. \
- if $e$ has a unique action $a$ maximizing its utility in $s$, as an utilitarian ethic requires to maximize its utility, the only allowed action is $a$, which leaves no freedom. \
- if $e$ leaves no freedom in $s$, then the only allowed action $a$ must maximize the utility function (by definition of utility function) and be the only action to do so. \
■
--MATH_END--

[//]: # Coq (44-80)
[//]: # Lean4 (50-106)

--MATH_START--
$\mathbf{Corollary}$\
A utilitarian ethic always has a unique action maximizing its utility iff it never leaves freedom.

$\mathbf{proof:}$\
Let $e$ be a utilitarian ethic, $uf$ its utility function. \
$e$ always has a unique action maximizing its utility \
$\iff \forall s \in S$, $e$ has a unique action maximizing its utility in $s$ \
$\iff \forall s \in S$, $e$ leaves no freedom in $s$ \
$\iff e$ never leaves freedom \
■
--MATH_END--

[//]: # Coq (82-94)
[//]: # Lean4 (108-127)
