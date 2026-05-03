---
title: "Maximizing work incentive"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - Economics
  - Taxation
...


## Presentation

It is often asked and investigated how make people as keen as possible to work. If one fixes the maximization of the incentive to work (as defined in [this article](https://leibnizproject.com/Articles/definition_capitalism_communism.html) as a desirable goal, pure capitalisms) unsurprisingly maximize this incentive, but they are far from being the only ones.

--MATH_START--
Throughout this page, let $I$ be the finite set of individuals (with $N$ as the number of individuals) and $gs \in \mathbb R$ is governement spendings.
--MATH_END--

[//]: # Lean4 (11-13)


## Average work incentive

The work incentive of an individual depends on the situation, so we consider its average over all these situations.

--MATH_START--
$\mathbf{Definition}$\
Let $r: {\mathbb R}^I \to {\mathbb R}^I$ be a redistribution. \
Let $i \in I$ be an individual. \
Let $c \in {\mathbb R}^I$ be a contribution profile. \
Let $a, b \in {\mathbb R}$ be quantities (representing individual contributions) such that $a \lt b$. \
If $wi = \frac {\mathrm{d} r(c_{i \leftarrow q})(i)} {\mathrm{d} q}$ is the work incentive of individual $i$, the average work incentive between $a$ and $b$ is
$$\frac 1 {b - a} \int_{a}^{b} wi(q) \, dq$$
By a mere substitution and the fundamental theorem of calculus, it equals
$$\frac {r(c_{i \leftarrow b})(i) - r(c_{i \leftarrow a})(i)} {b - a}$$
--MATH_END--

[//]: # Lean4 (18-65)

--MATH_START--
$\mathbf{Definition}$\
Let $r: {\mathbb R}^I \to {\mathbb R}^I$ be a redistribution. \
Let $i \in I$ be an individual. \
Let $c \in {\mathbb R}^I$ be a contribution profile. \
Let $wi \in {\mathbb R}^{\mathbb R}$ be the work incentive. \
Then the (global) average work incentive is defined as
$$\lim_{M \to +\infty} \frac 1 M \int_{0}^{M} wi(q) \, dq$$
It may not exist.
--MATH_END--

[//]: # Lean4 (67-74)


## Maximizing the average work incentive

In "conventional" situations, the average work incentive of an individual can not exceed 1. Otherwise, the accounts can not be in a balance whatever the work done by the individual.

--MATH_START--
$\mathbf{Proposition-Definition}$\
Let $r: {\mathbb R}^I \to {\mathbb R}^I$ be a redistribution. \
Let $i \in I$ be an individual. \
Let $c \in {\mathbb R}^I$ be a contribution profile. \
Let $wi \in {\mathbb R}^{\mathbb R}$ be the work incentive. \
Let $awi$ be the average work incentive. \
Let's suppose that $wi$ is differentiable with a continuous derivative and that the sum of retributions to all the individuals but $i$ is nonnegative from a certain contribution by $i$. \
Then $awi \le 1$. In such a case, $r$ is said to maximize the average work incentive.

$\mathbf{proof:}$\
$awi = \lim_{M \to +\infty} \frac 1 M \int_{0}^{M} wi(q) \, dq = \lim_{M \to +\infty} \frac {r(c_{i \leftarrow M})(i) - r(c_{i \leftarrow 0})(i)} M$ \
By the account equilibrium, we have $\sum_{j \in I} c_{i \leftarrow M}(j) = gs + \sum_{j \in I} r(c_{i \leftarrow M})(j)$, so that
$$\sum_{j \ne i} c(j) + M = gs + \sum_{j \ne i} r(c_{i \leftarrow M})(j) + r(c_{i \leftarrow M})(i)$$ and
$$r(c_{i \leftarrow M})(i) = \sum_{j \ne i} c(j) + M - gs - \sum_{j \ne i} r(c_{i \leftarrow M})(j)$$
By substitution, \
$$awi = \frac {\sum_{j \ne i} c(j) + M - gs - \sum_{j \ne i} r(c_{i \leftarrow M})(j) - r(c_{i \leftarrow 0})(i)} M$$ \
As the sum of retributions to all the individuals but $i$ is nonnegative from a certain contribution by $i$,
$$awi \le \lim_{M \to +\infty} \frac {\sum_{j \ne i} c(j) + M - gs - r(c_{i \leftarrow 0})(i)} M$$
which is $1$. \
■
--MATH_END--

[//]: # Lean4 (76-308)

Unsurprisingly, pure capitalisms maximize the work incentive.

--MATH_START--
$\mathbf{Lemma}$\
The average work incentive of pure capiptalisms is $1$ and thus maximize it.

$\mathbf{proof:}$\
$$\begin{align}
  awi &= \lim_{M \to +\infty} \frac {r(c_{i \leftarrow M})(i) - r(c_{i \leftarrow 0})(i)} M \\
      &= \lim_{M \to +\infty} \frac {M - \frac {gs} N - r(c_{i \leftarrow 0})(i)} M \\
      &= 1
\end{align}$$
■
--MATH_END--

[//]: # Lean4 (310-422)
