# cryptarithmetic-puzzles
Solving Cryptarithmetic puzzles with CLIPS

## What's CLIPS?

CLIPS is a declerative programing language (think prolog), a short snippet from their website:


Developed at NASA’s Johnson Space Center from 1985 to 1996, the C Language Integrated Production System (CLIPS) is a rule-based programming language useful for creating expert systems and other programs where a heuristic solution is easier to implement and maintain than an algorithmic solution.


You can get clips at http://www.clipsrules.net

##  Abstract
This repository covers an approach taken in order to solve cryptarithmetic addition problems along sided possible implementation decisions that can be made whilst using CLIPS language for this and general Constrain Satisfaction Problems.

## What is a cryptarithmetic puzzle?
Cryptarithmetic puzzles come in all shapes and forms, in this work, only addition of two numbers is considered.
An example of cryptarithmetic problem is something like:

   S E N D  
\+ M O R E  
\-----------  
M O N E Y  

Where the goal is to find a set of unique digits corresponding to each letter such that the equation is satisfied.

## Additional notes

The program does not take effort to validate that the input is in a correct format, therefore it is left for the user to make sure that the input follows basic cryptarithmetic problem rules.
Program allows to enter number base, but for these test particular examples it is assumed that the base is decimal.
Following inputs described in the appendix are all possible cryptarithmetic puzzles with at least one solution and the program correctly solves them all.

Full writeup can be found in the pdf file in the repo

## Summary

Rule-based implementation so solve CSP problems is clearly possible and offer readable and uncluttered code, but does not seem to be as efficient as say imperative implementation of the same algorithm. The constraints are not used actively whilst searching for the solution and there are particular difficulties expressing some constraints as the language does not support native way to express constraints such as disjunction constrains for example exclusive or for a set of variables.
