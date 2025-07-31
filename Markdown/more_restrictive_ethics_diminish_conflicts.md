---
title: "More restrictive individual ethics diminish the risk of conflicts"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy
  - ethics
  - society
...


## Presentation

In a society composed of individuals, it is proved here with given definitions that the more individuals have a restrictive in their personnal ethic, the less likely conflicts are.

One relies on [this article](https://leibnizproject.com/Articles/ethics_in_society.html).

--MATH_START--
Throughout this page, let $I$ be the finite set of individuals of a society, $S$ be the set of states, $A$ be the set of actions, $SubjS = S × I$ be the set of subjective states and $E = \{⊤, ⊥\}^{SubjS \times A}$ the set of ethics.
--MATH_END--

[//]: # Rocq (11-13)


## Feasability

We introduce the notion of practical fesability. For example, it's not possible that 30 persons simultaneously sit on a public bench.

--MATH_START--
$\mathbf{Definition}$\
Let $feasible$ be a function which at each $s \in S, (a_i) \in A^I$ associates $⊥$ if it's not concretely possible that each individuals $i$ does the $a_i$ action and $⊤$ if it is.

$\mathbf{Definition}$\
An action profile $(a_i) \in A^I$ is said compatible in state $s \in S$ if $feasible(s, (a_i)) = ⊤$ and incompatible if $feasible(s, (a_i)) = ⊥$.

$\mathbf{Definition}$\
$feasible$ is said to involve constraints in $s$ if $\exists (a_i) \in A^I, \neg feasible(s, (a_i))$.
--MATH_END--

[//]: # Rocq (14-26)


## Conflicts

If everyone can follow its own ethic then no one is an ethical dead end.

--MATH_START--
$\mathbf{Definition}$\
Let $s \in S, (e_i) \in E^I, (a_i) \in A^I$.
We say that everyone follows its ethic if $\forall i \in I, e_i((s, i), a_i)$.

$\mathbf{Lemma\text{ }1}$\
Let $s \in S, (e_i) \in E^I, (a_i) \in A^I.
If every individual follows its own ethic, then none of them is in an ethical dead end.

$\mathbf{proof:}$\
Let $s \in S$ and $i \in I$. \
As $i$ follows its own ethic, there is an $a \in A$ such that $e_i((s, i), a_i)$, so $i$ is not in an ethical dead end. \
■
--MATH_END--

[//]: # Rocq (28-41)

A conflict occurs when not every individual (following its own ethic) can do the action (s)he wants.

--MATH_START--
$\mathbf{Definition}$\
Let $s \in S, (e_i) \in E^I, (a_i) \in A^I$.
There is a conflict if
$$\begin{cases*}
  \neg feasible(s, (a_i)) \\
  \text{ everyone follows its ethic }
\end{cases*}$$
There is no conflict if
$$\begin{cases*}
  feasible(s, (a_i)) \\
  \text{ everyone follows its ethic }
\end{cases*}$$
--MATH_END--

[//]: # Rocq (43-51)

Conflict (and the absence of conflict) presuppose that everyone follows its own ethic, which is possible only if no one is an ethical dead end.

--MATH_START--
$\mathbf{Lemma\text{ }2}$\
If there is a conflict, then no individual is in an ethical dead end. \
If there is no conflict, then no individual is in an ethical dead end.

$\mathbf{proof:}$\
Let $s \in S$ and $i \in I$. \
In both cases, everyone follows its own ethic by definition, and we conclude with the previous lemma. \
■
--MATH_END--

[//]: # Rocq (53-71)


## More restrictive individual ethics diminish the risk of conflicts

If an individual ethic is replaced with a more restrictive one, this can't create a conflict.

--MATH_START--
$\mathbf{Proposition}$\
Let $s \in S, (e_i) \in E^I, (a_i) \in A^I, j \in I, e \in E$.
If $e_j$ is more restrictive than $e$ and $s, (e_i), (a_i)$ conflict, then $s, (e_i)_{j/e}, (a_i)$ conflict.

$\mathbf{proof:}$\
As $s, (e_i), (a_i)$ conflict, we have $\neg feasible(s, (a_i))$ and $\forall i \in I, e_i((s, i), a_i)$ by definition. \
As $e_j$ is more restrictive than $e$, we have $e((s, j), a_j)$. \
We can cconclude that $s, (e_i)_{j/e}, (a_i)$ conflict. \
■
--MATH_END--

[//]: # Rocq (73-92)

And if not everything is feasible, one can create a conflict by unrestricting a single individual ethic.

--MATH_START--
$\mathbf{Proposition}$\
Let $j \in I$.
If $feasible$ involves constraints, then $\exists s \in S, (e_i) \in E^I, (a_i) \in A^I, e \in E,$ such that
$$\begin{cases*}
  e_j \text{ is more restrictive than } e \text{ in subjective state } (s, j) \\
  (e_i), (a_i) \text{ don't conflict in } s \\
  (e_i)_{j/e}, (a_i) \text{ conflict in } s
\end{cases*}$$

$\mathbf{proof:}$\
Let $s \in S, (a_i) \in A^I$ unfeasible. \
Let $(e_i) \in E^I$ defined in $s$ by (whatever state and action)
$$\begin{cases*}
  ⊥ \text{ if } i = j \\
  ⊤ \text{ otherwise }
\end{cases*}$$
Then, as $j$ doesn't act accordingly to its ethic, $(e_i), (a_i)$ don't conflict in $s$. \
Let $e \in E$ defined by $e((s, i), a) = ⊤ \text{ } \forall (s, i) \in SubjS, a \in A$. \
Then, as $e$ allows everything, $e_j$ is more restrictive than $e$. \
Now, $(e_i)_{j/e}((s, i), a) = ⊤ \text{ } \forall (s, i) \in SubjS, a \in A$, which creates a conflict together with the fact that $s, (a_i)$ is not feasible. \
■
--MATH_END--

[//]: # Rocq (94-148)
