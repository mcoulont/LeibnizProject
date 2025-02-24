---
title: 'Every ethic without dead end is utilitarian'
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy
  - ethics
  - utility-function
...


## Presentation

An ethic being the rule of conduct which tells in each given situation if an action is ethical or not, it is proved here that every ethic is utlitarian, in the sense that it maximizes a [utility function](https://en.wikipedia.org/wiki/Utility#Preference).


## Definition of an ethic

Being given a situation (also named state following the usual terminology in artificial intelligence: see [this Wikipedia page](https://en.wikipedia.org/wiki/Intelligent_agent#Objective_function) for example), an ethic tells if the action is right or wrong in the situation.

--MATH_START--
Throughout this page, let $S$ be the state of states and $A$ the set of actions.

$\mathbf{Definition}$\
An ethic is a function from $S × A$ to $\{⊥ ,⊤\}$, where $⊥$ is the image for actions being unethical and $⊤$ the one for ethical actions.
--MATH_END--

[//]: # (2-11)

An ethic without dead end is an ethic which lets you at least one ethical action in each situation. Note that this is not an assumption of hope: such a possible action can be "do nothing". It seems possible to assume that every ethic has no dead end (or at least can be slightly modified to remove them, for example adding as ethical action "kill oneself" to situations having none).

--MATH_START--
$\mathbf{Definition}$\
An ethic $e: S × A \to \{⊥ ,⊤\}$ has no dead end if $\forall s \in S$ there is $a in A$ such that $e(s, a) = ⊤$.
--MATH_END--

[//]: # (13-14)


## Definition of a utility function

We may have in each situation a preference among all the alternatives of actions.

--MATH_START--
$\mathbf{Definition}$\
A preference order is a total and transitive binary relation. We will in this page denote with $a_1 \ge a_2$ the fact that the alternative $a_1$ is preferable (or equally preferable) to an alternative $a_2$.
--MATH_END--

[//]: # (16-24)

A utility function gives preferences among all possible alternatives. In our context, you may see this utility function as a measure of the "goodness" of actions.

--MATH_START--
$\mathbf{Definition}$\
A utility function is a function from a set $A$ of alternatives to a set $U$ endowed with a preference order. In our context, the alternatives are the possible actions in each given situation, and a utility function is from $S × A$ to $U$. Strictly speaking, we have a utility function for each state.

Note that the usual utility functions are given with $U$ being the real numbers endowed with the usual $\ge$ operator. We deal with (arguably) the most general definition.
--MATH_END--

[//]: # (26-33)


## Definition of an utilitarian ethic

An ethic is said to maximize a utility function if for each situation it imposes the action with the maximum goodness. There may be more than one such action.

--MATH_START--
$\mathbf{Definition}$\
An ethic $e$ maximizes a utility function $u$ if
$$\forall s \in S,\ \forall a \in A,\ e(s, a)=⊤ \iff \forall a' \in A,\ u(a) \ge u(a')$$
--MATH_END--

[//]: # (35-46)

An ethic is said to be utilitarian if it maximizes a utility function.

--MATH_START--
$\mathbf{Definition}$\
An ethic $e$ is utilitarian if there is a utility function $u$ such that $e$ maximizes $u$.
--MATH_END--

[//]: # (48-52)


## Proving that every ethic (without dead end) is utilitarian

An ethic being given, we can for each situation assign the value $1$ to the approved action(s) and $0$ to the disapproved ones.

--MATH_START--
$\mathbf{Definition}$\
An ethic $e$ being given, its associated utility is the following function:
$$\begin{align*}
    S × A &\to \mathbb R\\
    (s, a) &\mapsto \begin{cases*}
        1 \text{ if } e(s, a) = ⊤ \\
        0 \text{ if } e(s, a) = ⊥
    \end{cases*}
\end{align*}$$
--MATH_END--

[//]: # (54-82)

If the ethic has no dead end, this gives a utility function it maximizes.

--MATH_START--
$\mathbf{Proposition}$\ 
Every ethic without dead end is utilitarian.

$\mathbf{proof:}$\
Let $e$ be an ethic without dead end. \
By definition of utilitarian, it suffices to show that $e$ maximizes its associated utility (which we note $au$), that is: \
$$\forall s \in S,\ \forall a \in A,\ e(s, a)=⊤ \iff \forall a' \in A,\ au(a) \ge au(a')$$
Let $s \in S$ and $a \in A$. \
As $e$ has no dead end, by definition of the associated utility, there is an action whose image by $au$ is $1$, which is thus the maximum value of $au$ (because the other possible value is $0$), that is: \
$$\forall a' \in A,\ au(a) \ge au(a') \iff au(a) = 1$$
And $e(s, a)=⊤ \iff au(a) = 1$ results from the definition of the associated utility
■
--MATH_END--

[//]: # (84-108)

