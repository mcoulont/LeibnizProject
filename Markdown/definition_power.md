---
title: "A definition of power"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy
...


## Presentation

Here is formalized the concept of power of an individual in a society.

One relies mostly on [this article](https://leibnizproject.com/Articles/ethics_in_society.html) and [this one](https://leibnizproject.com/Articles/occam_razor.html).

--MATH_START--
Throughout this page, let $T$ be the set of instants in the unfolding of time. If $t, t' \in T$, $t \le t'$ means that the instant $t$ is before (or simultaneous with) $t'$. \
Let $I$ the finite set of individuals of a society, $S$ be the set of states and $A$ the set of actions an individual can do.
--MATH_END--

[//]: # Rocq (11-15)


## Individual policies

An individual policy is the line of conduct of an individual: what the individual does depending on the situation.

--MATH_START--
$\mathbf{Definition}$\
Let $h$ be a history and $\sigma$ a permutation of $S_I$. \
Then the history $h_\sigma$ is defined as:
$$\begin{align*}
    T &\to \mathbb S × A^I\\
    t &\mapsto h(t)_\sigma
\end{align*}$$

$\mathbf{Definition}$\
Let $e$ be an event and $\sigma$ a permutation of $S_I$. \
Then the event $e_\sigma$ is defined as:
$$\begin{align*}
    H = (S × A^I)^T &\to \mathbb \{⊤, ⊥\}\\
    h &\mapsto e(h_\sigma)
\end{align*}$$

$\mathbf{Definition}$\
The set $P$ of individual policies is the set of functions from histories (before some instant) to actions.

$\mathbf{Definition}$\
An individual $i \in I$ is said to follow a policy in a history if at each instant its action is the one given by the policy.
--MATH_END--

[//]: # Rocq (17-47)


## Goal fulfilling and power

An individual is more powerful than another it can achieve every single goal the other can.

--MATH_START--
$\mathbf{Definition}$\
A goal is said fulfilled by an individual in a history by a policy if it happens while the policy is followed.
--MATH_END--

[//]: # Rocq (49-54)

--MATH_START--
$\mathbf{Definition}$\
An individual may achieve a goal under a scientific theory if there is an individual policy and a history satisfying the scientific theory in which the goal is fulfilled by the individual by the policy.
--MATH_END--

[//]: # Rocq (56-63)

--MATH_START--
$\mathbf{Definition}$\
An individual $i \in I$ is said more powerful than another individual $j \in I$ in a state $s \in S$ under a scientific theory $st$ if for all goal $g$
$$j \text{ may achieve } g \text{ under } st \Rightarrow i \text{ may achieve } g_\sigma \text{ under } st$$
And an individual $i \in I$ is said strictly more powerful than another individual $j \in I$ in a state $s \in S$ under a scientific theory $st$ if it's more powerful and there is a goal achievable by $i$ but not by $j$.
--MATH_END--

[//]: # Rocq (65-86)
