---
title: "Pure capitalism is the only redistribution which makes financially independent"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - Economics
  - Taxation
...


## Presentation

If one wants to get a retribution independent of what other individuals do, only pure capitalism fits.

One relies on [this article](https://leibnizproject.com/Articles/definition_capitalism_communism.html).

--MATH_START--
Throughout this page, let $I$ be the finite set of individuals (with $N$ as the number of individuals) and $gs \in \mathbb R$ is governement spendings.
--MATH_END--

[//]: # Lean4 (6-8)

--MATH_START--
$\mathbf{Definition}$\
It is said that own retribution depends only on own contribution in a redistribution $r : {\mathbb R}^I \to {\mathbb R}^I$ if
$$\exists f \in {\mathbb R}^{\mathbb R} \text{ such that } \forall c \in {\mathbb R}^I, i \in I, r(c)(i) = f(c(i))$$
--MATH_END--

[//]: # Lean4 (13-18)

--MATH_START--
$\mathbf{Lemma}$\
Own retribution depends only on own contribution in pure capitalisms.

$\mathbf{proof:}$\
Take $f = c \mapsto c - \frac {gs} N$. \
Own retribution does not depend on contributions of other individuals. \
■
--MATH_END--

[//]: # Lean4 (20-39)

--MATH_START--
$\mathbf{Proposition}$\
Own retribution depends only on own contribution only in pure capitalisms.

$\mathbf{proof:}$\
If $r$ is a redistribution in which own retribution depends only on own contribution, let $f : {\mathbb R} \to {\mathbb R}$ be the function giving the individual's retribution from its contribution. \
Let $c \in {\mathbb R}$. In a situation where everyone contributes up to $c$, wealth conservation gives $N \times c + gs = N \times f(c)$, so that $f(c)=c - \frac {gs} N$. \
■
--MATH_END--

[//]: # Lean4 (31-83)
