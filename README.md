# ICCAD 2023 Problem A
## Document
[ICCAD 2023 Problem A report](https://docs.google.com/document/d/1IwRJmWurMKUFpEzGPRlqsisgXPsYYjdKnI81r-mT59s/edit)

[CAD討論進度](https://docs.google.com/document/d/1_S91WvefRApemSWcJEM14oBDBZ7n9NKA2SnN2d04OFc/edit)

## Main Algorithm
* One matching 
if problem size is **too large** $\rightarrow$ ***it is not pratical to find all possible matching***
iteratively update current optimal matching until 3500 seconds and output current optimal matching
![](https://i.imgur.com/kkqAPN7.png)

* All matching
if problem size is **not too large** $\rightarrow$ find **all possible matching** at once and find optimal matching
![](https://i.imgur.com/vDqvAjW.png)

## Usage

### Compile
#### Build up library abc: 
./SETUP.sh 

#### After build up abc then make:
make

### Execution

#### Run specific test file
./bmatch "input" "match" : run "input" file and output result to "match"

exemple : ./bmatch input match

#### Clean all produced file
make clean
   


