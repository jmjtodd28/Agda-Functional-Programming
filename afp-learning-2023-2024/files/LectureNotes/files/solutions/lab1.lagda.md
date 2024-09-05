# Week 1 Lab Lecture

## Learning objectives

 * **[Install Agda](files/Resources/resources.md) in your own computer.**

 * Learn how to use the emacs [interactive Agda mode](https://my-agda.readthedocs.io/en/latest/getting-started/quick-guide.html).

 * [Basic emacs](https://www.gnu.org/software/emacs/refcards/pdf/refcard.pdf).

 * Basic Agda interactive mode in emacs.

 * Run Agda in the LG04 lab.

Agda has an interactive mode that is based on the text editor [emacs](files/Resources/resources.md). The objective of this lab is to begin to learn it.
There is also a [plugin for VS Code](resources.md), but we haven't tried it.

## Important

The assessed tests for this module will be conducted exclusively in the School of Computer Science lab machines, and so it is important that you learn how to work in Agda with the lab machines, even if you plan to install Agda in your own machine for study purposes.

## Connecting remotely to the lab to use Agda

If you don't have Agda installed in your own computer, you can use it remotely in our labs.

 1. Open a terminal.

 1. Connect to the gateway machine `tinky-winky` by typing

    `$ ssh username@tw.cs.bham.ac.uk`

    * Your username should be in *lowercase* and is the same as your university username.

 1. Once you are in `tinky-winky`, you need to go to the UG04 lab:

    `$ ssh-lab`

    * This will take you to a random lab machine.

    * The randomness is to balance the load.

 1. Now you should be logged in some lab machine. Type

 1. Then follow the instructions below.

## Using Agda in a lab


   * In a terminal, run

    `$ module load agda`.

    * This will make agda available.

    * You need to do this *every time* you login to the lab, whether you do this remotely or locally.

    * You can do this automatically by adding it to the hidden file `.login`. We'll demonstrate how to do it with `emacs` during the lab lecture.

 1. After this, type

    `$ agda-mode setup`

    * You will need to this *only once*, but it doesn't harm if you do it repeatedly.

 1. After this, we will need to do some configuration so that `emacs` recognizes `.lagda.md` files and so that two Agda keyboard shortcuts are registered properly over `ssh`.
    You will need to do this only once. Type

    `$ emacs .emacs`

    * Add the lines
      ```terminal
      (add-to-list 'auto-mode-alist '("\\.lagda.md\\'" . agda2-mode))

      (add-hook 'agda2-mode-hook
	  (lambda () (progn
		       (local-set-key (kbd "C-c ,") 'agda2-goal-and-context)
		       (local-set-key (kbd "C-c .") 'agda2-goal-and-context-and-inferred))))
      ```
      anywhere.

    * Type `ctrl-x ctrl-s` to save the file.

    * Type `ctrl-x ctrl-c` to quit emacs.

## Clone the module GitLab repository

You will need this step both in a lab machine and in your own machine.

 1. Have you already generated an ssh key for the School git? If so, skip this step.

    In a terminal, run the following command:

    ```terminal
    $ setup-git
    ```

    Now paste the key shown in the terminal at the page [GitLab SSH Keys](https://git.cs.bham.ac.uk/-/profile/keys)


 1. Now we will clone the AFP GitLab repository. You will need to do it only once in the lab machines.

    ```terminal
    $ git clone git@git.cs.bham.ac.uk:afp/afp-learning-2023-2024.git
    ```

    * We assume that you learned the basics of `git` in the module Functional Programming and possibly in other modules.

    * You will need to `git pull` regularly, as we update this repository regularly, in particular to get the weekly exercises.

    * **Don't modify** any of the existing files as you will get conflicts.

    * If you want to experiment with any of the provided files, which you should certainly do when you are studying, make a copy of the file with a new name. Don't forget to change the line `module filename where` with the new name you have chosen.

## Editing your first Agda file

 1. Now let's edit our first Agda file from the terminal.

    ```terminal
    $ cd ~/afp-learning-2023-2024/files/LectureNotes/files/exercises
    $ cp lab1.lagda.md my-lab1.lagda.md
    $ emacs my-lab1.lagda.md
    ```

    * Now you should be seeing this file in emacs. Find this position and start working following our verbal instructions.

    * In a browser, go to [Key bindings](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#keybindings).

    * In a browser, open [Emacs reference card](https://www.gnu.org/software/emacs/refcards/pdf/refcard.pdf).

## `ctrl-g ctrl-g`

You will need to type this when you start a sequence of emacs commands and then you want to give up without completing the sequence.

## Our first Agda file

Within emacs now type `ctrl-c ctrl-l`. This will "load" the Agda file and check it for correctness. The following program fragment has holes that we will fill interactively using the emacs mode for Agda. You can cheat by looking at the handout [introduction](/files/LectureNotes/files/introduction.lagda.md). But you *should not* copy and paste. Instead, you should learn and use the interactive mode following the lecturers verbal and visual instructions.

```agda
module solutions.lab1 where

Type = Set

data Bool : Type where
 true false : Bool

data Maybe (A : Type) : Type where
 nothing : Maybe A
 just    : A → Maybe A

data Either (A B : Type) : Type where
 left  : A → Either A B
 right : B → Either A B

data ℕ : Type where
 zero : ℕ
 suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data List (A : Type) : Type where
 []   : List A
 _::_ : A → List A → List A

infixr 10 _::_

data BinTree (A : Type) : Type where
 empty : BinTree A
 fork  : A → BinTree A → BinTree A → BinTree A

data RoseTree (A : Type) : Type where
 fork : A → List (RoseTree A) → RoseTree A

not : Bool → Bool
not true  = false
not false = true

_&&_ : Bool → Bool → Bool
true  && y = y
false && y = false


_||_ : Bool → Bool → Bool
true  || y = true
false || y = y

infixr 20 _||_
infixr 30 _&&_

if_then_else_ : {A : Type} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

_+_ : ℕ → ℕ → ℕ
zero  + y = y
suc x + y = suc (x + y)

_*_ : ℕ → ℕ → ℕ
zero  * y = zero
suc x * y = x * y + y

infixr 20 _+_
infixr 30 _*_

length : {A : Type} → List A → ℕ
length []        = 0
length (x :: xs) = suc (length xs)

_++_ : {A : Type} → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

infixr 20 _++_

map : {A B : Type} → (A → B) → List A → List B
map f []        = []
map f (x :: xs) = f x :: map f xs

[_] : {A : Type} → A → List A
[ x ] = x :: []

reverse : {A : Type} → List A → List A
reverse []        = []
reverse (x :: xs) = reverse xs ++ [ x ]

rev-append : {A : Type} → List A → List A → List A
rev-append []        ys = ys
rev-append (x :: xs) ys = rev-append xs (x :: ys)

rev : {A : Type} → List A → List A
rev xs = rev-append xs []
```
