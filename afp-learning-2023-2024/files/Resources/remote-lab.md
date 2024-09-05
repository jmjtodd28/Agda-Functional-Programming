# Working at the School UG04 lab remotely from your own machine

## Installing `ssh`

### Linux

In Ubuntu, open a terminal and run
```
$ sudo apt install ssh
```
But this should be already installed by default.
This also works for many other Debian-based distributions of Linux.

If you use a different distribution of Linux, you may need to replace `apt` by the package manager of your distribution. Please check the documentation of your Linux distribution to learn how to install packages. But in any case the package will be called `ssh`.

### Mac

Assuming that you have the [Homebrew](https://brew.sh) package manager installed
on your Mac, running the following command should be sufficient:

```
$ brew install ssh
```

If you do not have Homebrew installed, you can install it with the command in the above link.

### Windows

Follow [Microsoft's instructions](https://docs.microsoft.com/en-us/windows-server/administration/openssh/openssh_install_firstuse).

## Connecting to the lab

Now, in any of Linux, Mac or Windows, open a command-line terminal and run
```
$ ssh username@tw.cs.bham.ac.uk
$ ssh-lab
$ module load agda
```
Before running Agda for the first time you have to do this:
```
$ agda-mode setup
```
After the first time you don't need to do this any longer. However, you need to do `module load agda` every time you login to a machine before start working.

Notice that `username` has to be in **lowercase**. Also, make sure you use your **School of Computer Science password** and password, if you set it to be **different** from the **University password**.

 * The first `ssh` is to connect to the student's gateway machine `tinky-winky`,
   abbreviated `tw`. You will get a terminal running there.

 * From this terminal, the command `ssh-lab` takes you to a random machine in the lab in
   room UG04 of the Computer Science building. The randomness is to balance the load of the lab machines.

 * In the lab machine terminal, the command `module load agda` will make Agda
   available.

Now you are ready to go.

## Workflow

 * Using the `cd` command, navigate to the directory where your Agda files are or will be.

 * Look at this [`cd` tutorial](https://linuxize.com/post/linux-cd-command/) if you need.

 * More terminal commands that are used frequently are [here](https://www.hostinger.co.uk/tutorials/linux-commands) and [here](https://swcarpentry.github.io/shell-novice/reference.html) and Google can also help you.

 * Run `emacs somefile.agda` from the terminal. You will be able to create Agda programs and have them checked from there.

 * If you press `ctrl-z` you will get back to the terminal without closing emacs and making it into a background process. To get back to emacs, run the command `fg` (foreground).

 * When you are done, you can quit emacs with `ctrl-x ctrl-c`.

 * Then you can run `logout` to close the ssh connection, and `logout` again to close the first one.
