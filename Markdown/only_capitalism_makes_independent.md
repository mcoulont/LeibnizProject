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
Throughout this page, let $I$ be the finite set of individuals (with $N$ as the number of individuals).
--MATH_END--

[//]: # Lean4 (7-9)

--MATH_START--
$\mathbf{Definition}$\
It is said that own retribution depends only on own contribution in a redistribution $r : {\mathbb R}^I \to {\mathbb R}^I$ if
$$\exists f \in {\mathbb R}^{\mathbb R} \text{ such that } \forall c \in {\mathbb R}^I, i \in I, r(c)(i) = f(c(i))$$
--MATH_END--

[//]: # Lean4 (14-19)

--MATH_START--
$\mathbf{Lemma}$\
Own retribution depends only on own contribution in pure capitalism.

$\mathbf{proof:}$\
Own retriubtion is own contribution and thus does not depend on contributions of other individuals (take $f = id$). \
■
--MATH_END--

[//]: # Lean4 (21-27)

--MATH_START--
$\mathbf{Proposition}$\
Own retribution depends only on own contribution only in pure capitalism.

$\mathbf{proof:}$\
If $r$ is a redistribution in which own retribution depends only on own contribution, let $f : {\mathbb R} \to {\mathbb R}$ be the function giving the individual's retribution from its contribution. \
Let $c \in {\mathbb R}$. In a situation where everyone contributes up to $c$, wealth conservation gives $N \times c = N \times f(c)$, so that $f(c)=c$. \
■
--MATH_END--

[//]: # Lean4 (29-66)
