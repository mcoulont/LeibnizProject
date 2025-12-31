---
title: "A definition of intelligence"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - Philosophy
...


## Presentation

Here is formalized the concept of intelligence of an agent in a deterministic evironment.

One relies on [this article](https://leibnizproject.com/Articles/occam_razor.html).

--MATH_START--
Throughout this page, let $T$ be the set of instants in the unfolding of time. If $t, t' \in T$, $t \le t'$ means that the instant $t$ is before (or simultaneous with) $t'$. \
Let $S$ be the set of states and $A$ the set of actions the agent can do.
--MATH_END--

[//]: # Rocq (7-10)


## Policies

A policy is a line of conduct: what the agent does depending on the situation.

--MATH_START--
$\mathbf{Definition}$\
The set $P$ of policies is the set of functions from histories (before some instant) to actions.

$\mathbf{Definition}$\
A history is said to follow a policy if at each instant the action done is the one given by the policy. \
With $t_0 \in T$, a history before $t_0$ is said to follow a policy before $t_0$ if at each instant before $t_0$ the action done is the one given by the policy.
--MATH_END--

[//]: # Rocq (12-31)

Given a goal, one establishes a policy in order to reach it.

--MATH_START--
$\mathbf{Definition}$\
The set $STR$ of strategizings is the set of functions from events (goals) to policies.
--MATH_END--

[//]: # Rocq (33-34)


## Goal fulfilling, adequateness to reach goals and intelligence

A policy is more adequate than another to reach a goal if its failure implies the failure of the other one. And one is more intelligent if one elaborates a more adequate policy whatever the goal.

These two definitions do not work in [non-deterministic environments](https://leibnizproject.com/Articles/physical_theories.html). Indeed, if there is some randomness, a goal may be reached thanks to beginner's luck: an action which is not the most likely to achieve the goal may succeed because something unexpected (but still possible) happened. And in deerministic environments, good decisions taken for bad reasons are regarded as intelligent.

--MATH_START--
$\mathbf{Definition}$\
A goal is said fulfilled in a history by a policy if it happens while the policy is followed. \
A goal is said fulfilled in a history before $t_0 \in T$ by a policy if it happened before $t_0$ while the policy is followed.
--MATH_END--

[//]: # Rocq (36-48)

--MATH_START--
$\mathbf{Definition}$\
A policy may achieve a goal under a scientific theory if there is a history satisfying the scientific theory in which the goal is fulfilled.
--MATH_END--

[//]: # Rocq (50-56)

--MATH_START--
$\mathbf{Definition}$\
A scientific theory $st$ being given, a policy $p_1 \in P$ is said more adequate than $p_2 \in P$ to achieve a goal $g$ if
$$g \text{ is fulfilled in some history satisfying } st \text{ following } p_2 \Rightarrow g \text{ is fulfilled in some history satisfying } st \text{ following } p_1$$
--MATH_END--

[//]: # Rocq (58-63)

--MATH_START--
$\mathbf{Definition}$\
A scientific theory $st$ being given, a strategizing $str_1 \in STR$ is said more intelligent than $str_2 \in STR$ if, whatever the goal, it provides a more adequate policy.
--MATH_END--

[//]: # Rocq (65-83)
