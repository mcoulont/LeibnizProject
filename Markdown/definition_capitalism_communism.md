---
title: "A definition of capitalism and communism in terms of redistribution of wealth"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - Economics
...


## Presentation

With wealth being represented as money (that is as a number):
- purely capitalist redistribution just retributes every individual up to its contribution
- purely ccommunist redistribution equally retributes every individual, whatever its contribution.

--MATH_START--
Throughout this page, let $I$ be the finite set of individuals. \
Contributions by individuals are represented by their monetary value, which is a real number (potentially negative, in case of vandalism for example). So are retributions to individuals.
--MATH_END--

[//]: # Rocq (14-18)


## Redistribution

In a society people work, contributing to the community up to a magnitude typically defined by the law of supply and demand. Then the society redistributes the produced wealth (under the form of money in our model).

--MATH_START--
$\mathbf{Definition}$\
Being given a profile of contributions made by every individual $c \in {\mathbb R}^I$, a redistribution function returns a retribution $r \in {\mathbb R}^I$, which is the money given back to every individual, with the constraint of wealth conservation: $\sum_{i \in I} c(i) = \sum_{i \in I} r(i)$.
--MATH_END--

[//]: # Rocq (20-34)


## Capitalism and communism

Pure capitalism retributes every individual up to his contribution.

--MATH_START--
$\mathbf{Definition}$\
Pure capitalism is the redistribution defined by
$$\begin{align*}
    {\mathbb R}^I &\to {\mathbb R}^I\\
    c &\mapsto c
\end{align*}$$
--MATH_END--

[//]: # Rocq (36-47)

Pure communism retributes every individual the same amount, regardless of its contribution.

--MATH_START--
$\mathbf{Definition}$\
Pure communism is the redistribution defined by
$$\begin{align*}
    {\mathbb R}^I &\to {\mathbb R}^I\\
    c &\mapsto ({i_0 \in I} &\mapsto \frac {\sum_{i \in I} c(i)} N)
\end{align*}$$
(where $N$ is the number of individuals).
--MATH_END--

[//]: # Rocq (49-78)


## Egalitarian redistributions

A redistribution is egalitarian if the retribution to every individual doesn't depend on who the individual is. Everyone receives equal treatment.

--MATH_START--
$\mathbf{Definition}$\
The redistribution $r: {\mathbb R}^I \to {\mathbb R}^I$ is said egalitarian if
$$\forall σ \in S_I, c \in {\mathbb R}^I, {r(c)}_σ = r(c_σ)$$
(where $S_I$ denotes the set of permutations on $I$ and $d_σ(i) = d(σ(i))$ $\forall d \in {\mathbb R}^I, σ \in S_I$).
--MATH_END--

[//]: # Rocq (80-83)

As in pure capitalism everyone is retributed depending solely on its contribution, it is egalitarian.

--MATH_START--
$\mathbf{Lemma}$\
Pure capitalism is egalitarian.

$\mathbf{proof:}$\
$\forall σ \in S_I, c \in {\mathbb R}^I, {r(c)}_σ = i \mapsto r(c)(σ(i) = i \mapsto c(σ(i)) = i \mapsto r(c(σ(i))) = r(c_σ)$. \
■
--MATH_END--

[//]: # Rocq (85-89)

Pure communism is unsurprisingly egalitarian as well.

--MATH_START--
$\mathbf{Lemma}$\
Pure communism is egalitarian.

$\mathbf{proof:}$\
$\forall σ \in S_I, c \in {\mathbb R}^I, {r(c)}_σ = \frac {\sum_{i \in I} c(i)} N = r(c_σ)$. \
■
--MATH_END--

[//]: # Rocq (91-102)


## Work incentive

An individual is encouraged to work if increasing its contribution increases its retribution as well.

--MATH_START--
$\mathbf{Definition}$\
The redistribution $r: {\mathbb R}^I \to {\mathbb R}^I$ is said to encourage the work if
$$\forall c \in {\mathbb R}^I, i \in I, c' \in {\mathbb R} \text{ such that } c(i) < c', r(c)(i) < r(c_{i \leftarrow c'})(i)$$
(where $c_{i \leftarrow c'}$ denotes the profile of contributions $c$ in which $i$'s contribution is replaced with $c'$).
--MATH_END--

[//]: # Rocq (104-107)

Pure capitalism encourages the work as increasing one's contribution increases one's retribution up to the same amount.

--MATH_START--
$\mathbf{Lemma}$\
Pure capitalism encourages the work.

$\mathbf{proof:}$\
$\forall c \in {\mathbb R}^I, i \in I, c' \in {\mathbb R} \text{ such that } c(i) < c', r(c)(i) = c(i) < c' = r(c_{i \leftarrow c'})(i)$. \
■
--MATH_END--

[//]: # Rocq (109-118)

Pure communism encourages the work but the reward is divided by the number of individuals.

--MATH_START--
$\mathbf{Lemma}$\
Pure communism encourages the work.

$\mathbf{proof:}$\
$\forall c \in {\mathbb R}^I, i \in I, c' \in {\mathbb R} \text{ such that } c(i) < c', r(c)(i) = \frac {\sum_{j \in I} c(j)} N < \frac {(\sum_{j \ne i \in I} c(j)) + c'} N = r(c_{i \leftarrow c'})(i)$. \
■
--MATH_END--

[//]: # Rocq (120-164)
