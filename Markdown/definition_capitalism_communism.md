---
title: "A definition of capitalism and communism in terms of redistribution of wealth"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - Economics
  - Taxation
...


## Presentation

With wealth being represented as money (that is as a number):
- purely capitalist redistribution just retributes every individual up to its contribution
- purely ccommunist redistribution equally retributes every individual, whatever its contribution.

--MATH_START--
Throughout this page, let $I$ be the finite set of individuals (with $N$ as the number of individuals). \
Contributions by individuals are represented by their monetary value, which is a rational number (potentially negative, in case of vandalism for example). So are retributions to individuals.
--MATH_END--

[//]: # Rocq (14-18)


## Redistribution

In a society people work, contributing to the community up to a magnitude typically defined by the law of supply and demand. Then the society redistributes the produced wealth (under the form of money in our model).

--MATH_START--
$\mathbf{Definition}$\
Being given a profile of contributions made by every individual $c \in {\mathbb Q}^I$, a redistribution function returns a retribution $r \in {\mathbb Q}^I$, which is the money given back to every individual, with the constraint of wealth conservation: $\sum_{i \in I} c(i) = \sum_{i \in I} r(i)$.
--MATH_END--

[//]: # Rocq (20-34)


## Capitalism and communism

Pure capitalism retributes every individual up to his contribution.

--MATH_START--
$\mathbf{Definition}$\
Pure capitalism is the redistribution defined by
$$\begin{align*}
    {\mathbb Q}^I &\to {\mathbb Q}^I\\
    c &\mapsto c
\end{align*}$$
--MATH_END--

[//]: # Rocq (36-47)

Pure communism retributes every individual the same amount, regardless of its contribution.

--MATH_START--
$\mathbf{Definition}$\
Pure communism is the redistribution defined by
$$\begin{align*}
    {\mathbb Q}^I &\to {\mathbb Q}^I\\
    c &\mapsto ({i_0 \in I} &\mapsto \frac {\sum_{i \in I} c(i)} N)
\end{align*}$$
--MATH_END--

[//]: # Rocq (49-73)


## Egalitarian redistribution

A redistribution is egalitarian if the retribution to every individual doesn't depend on who the individual is. Everyone receives equal treatment.

--MATH_START--
$\mathbf{Definition}$\
The redistribution $r: {\mathbb Q}^I \to {\mathbb Q}^I$ is said egalitarian if
$$\forall σ \in S_I, c \in {\mathbb Q}^I, {r(c)}_σ = r(c_σ)$$
(where $S_I$ denotes the set of permutations on $I$ and $d_σ(i) = d(σ(i))$ $\forall d \in {\mathbb Q}^I, σ \in S_I$).
--MATH_END--

[//]: # Rocq (75-78)

As in pure capitalism everyone is retributed depending solely on its contribution, it is egalitarian.

--MATH_START--
$\mathbf{Lemma}$\
Pure capitalism is egalitarian.

$\mathbf{proof:}$\
$\forall σ \in S_I, c \in {\mathbb Q}^I, {r(c)}_σ = i \mapsto r(c)(σ(i) = i \mapsto c(σ(i)) = i \mapsto r(c(σ(i))) = r(c_σ)$. \
■
--MATH_END--

[//]: # Rocq (80-84)

Pure communism is unsurprisingly egalitarian as well.

--MATH_START--
$\mathbf{Lemma}$\
Pure communism is egalitarian.

$\mathbf{proof:}$\
$\forall σ \in S_I, c \in {\mathbb Q}^I, {r(c)}_σ = \frac {\sum_{i \in I} c(i)} N = r(c_σ)$. \
■
--MATH_END--

[//]: # Rocq (86-100)


## Work incentive

An individual is encouraged to work if increasing its contribution increases its retribution as well.

--MATH_START--
$\mathbf{Definition}$\
The redistribution $r: {\mathbb Q}^I \to {\mathbb Q}^I$ is said to encourage the work if
$$\forall c \in {\mathbb Q}^I, i \in I, c' \in {\mathbb Q} \text{ such that } c(i) < c', r(c)(i) < r(c_{i \leftarrow c'})(i)$$
(where $c_{i \leftarrow c'}$ denotes the profile of contributions $c$ in which $i$'s contribution is replaced with $c'$).
--MATH_END--

[//]: # Rocq (102-106)

Pure capitalism encourages the work as increasing one's contribution increases one's retribution up to the same amount.

--MATH_START--
$\mathbf{Lemma}$\
Pure capitalism encourages the work.

$\mathbf{proof:}$\
$\forall c \in {\mathbb Q}^I, i \in I, c' \in {\mathbb Q} \text{ such that } c(i) < c', r(c)(i) = c(i) < c' = r(c_{i \leftarrow c'})(i)$. \
■
--MATH_END--

[//]: # Rocq (108-117)

Pure communism encourages the work but the reward is divided by the number of individuals.

--MATH_START--
$\mathbf{Lemma}$\
Pure communism encourages the work.

$\mathbf{proof:}$\
$\forall c \in {\mathbb Q}^I, i \in I, c' \in {\mathbb Q} \text{ such that } c(i) < c', r(c)(i) = \frac {\sum_{j \in I} c(j)} N < \frac {(\sum_{j \ne i \in I} c(j)) + c'} N = r(c_{i \leftarrow c'})(i)$. \
■
--MATH_END--

[//]: # Rocq (119-163)


## Linear redistribution

A redistribution is linear if multiplying all the contributions by the same factor multiplies all the retributions accordingly. This is the same as saying that the redistribution does not change with a currency change. Pure capitalism and pure communism are linear.

--MATH_START--
$\mathbf{Definition}$\
The redistribution $r: {\mathbb Q}^I \to {\mathbb Q}^I$ is said linear if
$$\forall c \in {\mathbb Q}^I, k \in {\mathbb Q}, r(k c) = k r(c)$$
(where $k c$ denotes $c$ where all the individual contributions are multiplied by $k$)
--MATH_END--

[//]: # Rocq (165-172)

--MATH_START--
$\mathbf{Lemma}$\
Pure capitalism is linear.

$\mathbf{proof:}$\
$r(k c) = k c = k r(c)$. \
■
--MATH_END--

[//]: # Rocq (174-182)

--MATH_START--
$\mathbf{Lemma}$\
Pure communism is linear.

$\mathbf{proof:}$\
$r(k c) = i \mapsto \frac {\sum_{j \in I} k c(j)} N = i \mapsto k \frac {\sum_{j \in I} c(j)} N = k r(c)$. \
■
--MATH_END--

[//]: # Rocq (184-194)


## Fairness

A fair redistribution will retribute more to an individual who contributes more. Pure capitalism is oviously fair as one earns exactly what one contributes. For pure communism, it is not so as everyone earns the same whatever the work done.

--MATH_START--
$\mathbf{Definition}$\
The redistribution $r: {\mathbb Q}^I \to {\mathbb Q}^I$ is said fair if $\forall c \in {\mathbb Q}^I, i, j \in I, c(i) \le c(j) \Rightarrow$ r(i) \le r(j)$
And it is said strictly fair if $\forall c \in {\mathbb Q}^I, i, j \in I, c(i) \lt c(j) \Rightarrow$ r(i) \lt r(j)$
--MATH_END--

[//]: # Rocq (196-204)

--MATH_START--
$\mathbf{Lemma}$\
Pure capitalism is fair and strictly fair.

$\mathbf{proof:}$\
As $r(i) = c(i)$, the two implications are obvious. \
■
--MATH_END--

[//]: # Rocq (206-224)

--MATH_START--
$\mathbf{Lemma}$\
Pure communism is fair but not strictly fair (if there are at least two individuals).

$\mathbf{proof:}$\
$\forall i, j \in I, r(i) = r(j)$ which makes the first implication true. \
But it is not true that $r(i) \lt r(j)$ when $c(i) \lt c(j)$. \
■
--MATH_END--

[//]: # Rocq (226-250)
