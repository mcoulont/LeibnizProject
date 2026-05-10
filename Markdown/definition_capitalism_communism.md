---
title: "A definition of capitalism and communism in terms of redistribution of wealth"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - Economics
  - Taxation
...


## Presentation

Taxation permits to redistribute wealth between individuals in a society, drawing off the government's operating costs. \
With wealth being represented as money (that is as a number): \
- in pure capitalism, there is no operating cost and the redistribution just retributes every individual up to its contribution \
- in pure capitalism with operating costs equally divided between individuals (everyone pays the same tax), the redistribution retributes every individual up to its contribution, minus its share in the costs \
- purely ccommunist redistribution equally retributes every individual, whatever its contribution

--MATH_START--
Throughout this page, let $I$ be the finite set of individuals (with $N \gt 0$ as the number of individuals). \
Contributions by individuals are represented by their monetary value, which is a real number (potentially negative, in case of vandalism for example). So are retributions to individuals, and government spending.
--MATH_END--

[//]: # Lean4 (13-21)


## Redistribution

In a society people work, contributing to the community up to a magnitude typically defined by the law of supply and demand. Then the society redistributes the produced wealth (under the form of money in our model), minus its operating costs.

--MATH_START--
$\mathbf{Definition}$\
Being given government spending $gs \in \mathbb R$, a profile of contributions made by every individual $c \in {\mathbb R}^I$, a redistribution function returns a retribution $r \in {\mathbb R}^I$, which is the money given back to every individual, with the constraint of accounts at equilibrium: $\sum_{i \in I} c(i) = gs + \sum_{i \in I} r(i)$.
--MATH_END--

[//]: # Lean4 (23-38)


## Capitalism and communism

Pure capitalism retributes every individual up to his contribution, minus its share in (potential) operating costs, provided everyone is taxed up to the same amount.

--MATH_START--
$\mathbf{Definition}$\
Pure capitalism is the redistribution defined by
$$\begin{align*}
    {\mathbb R}^I &\to {\mathbb R}^I\\
    c &\mapsto c
\end{align*}$$
Pure capitalism with government spending $gs \in \mathbb R$ is the redistribution defined by
$$\begin{align*}
    {\mathbb R}^I &\to {\mathbb R}^I\\
    c &\mapsto ({i \in I} \mapsto c(i) - \frac {gs} N)
\end{align*}$$
Setting $gs$ to $0$ makes these two definitions coincide.
--MATH_END--

[//]: # Lean4 (40-85)

Pure communism retributes every individual the same amount, regardless of its contribution.

--MATH_START--
$\mathbf{Definition}$\
Pure communism is the redistribution defined by
$$\begin{align*}
    {\mathbb R}^I &\to {\mathbb R}^I\\
    c &\mapsto ({i_0 \in I} \mapsto \frac {(\sum_{i \in I} c(i)) - gs} N)
\end{align*}$$
--MATH_END--

[//]: # Lean4 (87-111)


## Egalitarian redistribution

A redistribution is egalitarian if the retribution to every individual doesn't depend on who the individual is. Everyone receives equal treatment.

--MATH_START--
$\mathbf{Definition}$\
The redistribution $r: {\mathbb R}^I \to {\mathbb R}^I$ is said egalitarian if
$$\forall σ \in S_I, c \in {\mathbb R}^I, {r(c)}_σ = r(c_σ)$$
(where $S_I$ denotes the set of permutations on $I$ and $d_σ(i) = d(σ(i))$ $\forall d \in {\mathbb R}^I, σ \in S_I$).
--MATH_END--

[//]: # Lean4 (113-118)

As in pure capitalisms everyone is retributed depending solely on its contribution, they are egalitarian.

--MATH_START--
$\mathbf{Lemma}$\
Pure capitalisms are egalitarian.

$\mathbf{proof:}$\
$\forall σ \in S_I, c \in {\mathbb R}^I, {r(c)}_σ = i \mapsto r(c)(σ(i)) = i \mapsto c(σ(i)) - \frac {gs} N = i \mapsto r(c(σ(i))) = r(c_σ)$. \
■
--MATH_END--

[//]: # Lean4 (120-125)

Pure communism is unsurprisingly egalitarian as well.

--MATH_START--
$\mathbf{Lemma}$\
Pure communism is egalitarian.

$\mathbf{proof:}$\
$\forall σ \in S_I, c \in {\mathbb R}^I, {r(c)}_σ = \frac {(\sum_{i \in I} c(i)) - gs} N = r(c_σ)$. \
■
--MATH_END--

[//]: # Lean4 (127-145)


## Work incentive

An individual is encouraged to work if increasing its contribution increases its retribution as well.

--MATH_START--
$\mathbf{Definition}$\
The redistribution $r: {\mathbb R}^I \to {\mathbb R}^I$ is said to encourage the work if
$$\forall c \in {\mathbb R}^I, i \in I, c' \in {\mathbb R} \text{ such that } c(i) < c', r(c)(i) < r(c_{i \leftarrow c'})(i)$$
(where $c_{i \leftarrow c'}$ denotes the profile of contributions $c$ in which $i$'s contribution is replaced with $c'$).
--MATH_END--

[//]: # Lean4 (147-153)

Pure capitalisms encourage the work as increasing one's contribution increases one's retribution up to the same amount.

--MATH_START--
$\mathbf{Lemma}$\
Pure capitalisms encourage the work.

$\mathbf{proof:}$\
$\forall c \in {\mathbb R}^I, i \in I, c' \in {\mathbb R} \text{ such that } c(i) < c', r(c)(i) = c(i) - \frac {gs} N < c' - \frac {gs} N = r(c_{i \leftarrow c'})(i)$. \
■
--MATH_END--

[//]: # Lean4 (155-165)

Pure communism encourages the work but the reward is divided by the number of individuals.

--MATH_START--
$\mathbf{Lemma}$\
Pure communism encourages the work.

$\mathbf{proof:}$\
$\forall c \in {\mathbb R}^I, i \in I, c' \in {\mathbb R} \text{ such that } c(i) < c', r(c)(i) = \frac {(\sum_{j \in I} c(j)) - gs} N < \frac {(\sum_{j \ne i \in I} c(j)) + c' - gs} N = r(c_{i \leftarrow c'})(i)$. \
■
--MATH_END--

[//]: # Lean4 (167-205)

The work incentive of an individual between two contributions is the difference between the corresponding retributions.

--MATH_START--
$\mathbf{Definition}$\
Let $r: {\mathbb R}^I \to {\mathbb R}^I$ be a redistribution. \
Let $i \in I$ be an individual. \
Let $q, q' \in {\mathbb R}$ be quantities (representing individual contributions) such that $q \lt q'$. \
Let $c \in {\mathbb R}^I$ be a contribution profile. \
The work incentive between contributions $q$ and $q'$ for $i$ is defined as
$$r(c_{i \leftarrow q'})(i) - r(c_{i \leftarrow q})(i)$$
--MATH_END--

[//]: # Lean4 (207-211)

--MATH_START--
$\mathbf{Definition}$\
Let $r: {\mathbb R}^I \to {\mathbb R}^I$ be a redistribution. \
Let $i \in I$ be an individual. \
Let $q \in {\mathbb R}$ be a quantity (representing an individual contribution). \
Let $c \in {\mathbb R}^I$ be a contribution profile. \
The instantaneous work incentive at contribution $q$ for $i$ is defined as
$$\frac {\mathrm{d} r(c_{i \leftarrow q})(i)} {\mathrm{d} q}$$
It may not exist, in case the function is not differentiable.
--MATH_END--

[//]: # Lean4 (213-227)

In pure capitalisms the work incentive between two contributions is just the difference between them.

--MATH_START--
$\mathbf{Lemma}$\
In pure capitalisms the work incentive between contributions $q$ and $q'$ for whatever individual is $q' - q$.

$\mathbf{proof:}$\
$(q' - \frac {gs} N) - (q - \frac {gs} N) = q' - q$. \
■
--MATH_END--

[//]: # Lean4 (229-241)

--MATH_START--
$\mathbf{Lemma}$\
In pure capitalisms the instantaneous work incentive is the function constant at $1$.

$\mathbf{proof:}$\
$\frac {\mathrm{d} r(c_{i \leftarrow q})(i)} {\mathrm{d} q} = \frac {\mathrm{d} (q - \frac {gs} N)} {\mathrm{d} q} = 1$. \
■
--MATH_END--

[//]: # Lean4 (243-252)

In pure communism the work incentive between two contributions is the difference between them divided by the number of individuals (the benefit of the extra work provided is split among individuals).

--MATH_START--
$\mathbf{Lemma}$\
In pure communism the work incentive between contributions $q$ and $q'$ for whatever individual is $\frac {q' - q} N$.

$\mathbf{proof:}$\
$r(c_{i \leftarrow q'})(i) - r(c_{i \leftarrow q})(i)$ \
$= \frac {q' + (\sum_{j \ne i \in I} c(j)) - gs} N - \frac {q + (\sum_{j \ne i \in I} c(j)) - gs} N$ \
$= \frac {(q' + (\sum_{j \ne i \in I} c(j)) - gs) - (q + (\sum_{j \ne i \in I} c(j)) - gs)} N$ \
$= \frac {q' - q} N$ \
■
--MATH_END--

[//]: # Lean4 (254-310)

--MATH_START--
$\mathbf{Lemma}$\
In pure communism the instantaneous work incentive is the function constant at $\frac 1 N$.

$\mathbf{proof:}$\
$\frac {\mathrm{d} r(c_{i \leftarrow q})(i)} {\mathrm{d} q} = \frac {\mathrm{d} (\frac {q + (\sum_{j \ne i \in I} c(j)) - gs} N)} {\mathrm{d} q} = \frac 1 N$. \
■
--MATH_END--

[//]: # Lean4 (312-396)


## Currency change

A currency change is just the multiplication of all amounts by a multiplier. This happened for example to countries having joined the euro area.

--MATH_START--
$\mathbf{Definition}$\
Subject to a currency change of multiplier $k \gt 0$, a redistribution $r: {\mathbb R}^I \to {\mathbb R}^I$ beconmes:
$$\begin{align*}
    {\mathbb R}^I &\to {\mathbb R}^I\\
    c &\mapsto k \times r(\frac c k)
\end{align*}$$
--MATH_END--

[//]: # Lean4 (398-501)


## Fairness

A fair redistribution will retribute more to an individual who contributes more. Pure capitalisms are oviously fair. For pure communism, it is not so as everyone earns the same whatever the work done.

--MATH_START--
$\mathbf{Definition}$\
The redistribution $r: {\mathbb R}^I \to {\mathbb R}^I$ is said fair if $\forall c \in {\mathbb R}^I, i, j \in I, c(i) \le c(j) \Rightarrow r(i) \le r(j)$
And it is said strictly fair if $\forall c \in {\mathbb R}^I, i, j \in I, c(i) \lt c(j) \Rightarrow r(i) \lt r(j)$
--MATH_END--

[//]: # Lean4 (503-515)

--MATH_START--
$\mathbf{Lemma}$\
Pure capitalisms are fair and strictly fair.

$\mathbf{proof:}$\
As $r(i) = c(i) - \frac {gs} N$, the two implications are obvious. \
■
--MATH_END--

[//]: # Lean4 (517-539)

--MATH_START--
$\mathbf{Lemma}$\
Pure communism is fair but not strictly fair (if there are at least two individuals).

$\mathbf{proof:}$\
$\forall i, j \in I, r(i) = r(j)$ which makes the first implication true. \
But it is not true that $r(i) \lt r(j)$ when $c(i) \lt c(j)$. \
■
--MATH_END--

[//]: # Lean4 (541-567)
