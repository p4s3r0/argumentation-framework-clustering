# ClustArg

## Introduction
ClustArg is a versatile tool designed with a focus on **abstract Argumentation Frameworks (AFs)**, providing a powerful platform for analyzing and computing different argumentation semantics. The tool is intended to help researchers and practitioners explore and evaluate abstract AFs, which represent the structure of argumentation without specifying the details of individual arguments. By implementing three core semantics—**conflict-free**, **admissible**, and **stable**—ClustArg enables the assessment of the acceptability and coherence of arguments within these abstract frameworks. Additionally, the tool supports refinements and two distinct extension calculation processes: **Breadth-First Search (BFS)** and **Depth-First Search (DFS)**, offering flexible approaches for analyzing AFs from different perspectives.

With ClustArg, users can:

- Compute the semantics of **concrete AFs**, providing insights into the acceptability of individual arguments and sets of arguments.
- Compute the semantics of **abstract AFs**, enabling the analysis of abstract argumentation structures without needing a fully instantiated set of arguments.
- Check if an **abstract AF is faithful**, ensuring that the abstract representation correctly reflects the structure of the argumentation.
- Compute **semantic extensions** and identify situations leading to **spuriousness**, where extensions may not align with expected logical behavior.
- Transform an AF that was initially spurious into one that is **faithful**, ensuring the argumentation structure is logically consistent and valid.

ClustArg is intended for researchers, developers, and anyone interested in exploring the dynamic landscape of argumentation frameworks and their semantics.

## Installation

ClustArg is coded in Python and includes a `requirements.txt` file for easy installation of dependencies. To set up the tool, simply follow these steps:

### 1. Clone this repository:

```bash
git clone https://github.com/p4s3r0/argumentation-framework-clustering.git
```

### 2. Navigate into the project directory:

```bash
cd argumentation-framework-clustering
```

### 3. (Optional but recommended) Set up a virtual environment to manage dependencies:

```bash
python3 -m venv venv
source venv/bin/activate  # On Windows use: venv\Scripts\activate
```

### 4. Install the required dependencies:

```bash
pip3 install -r requirements.txt
```

## Usage

### Generate Semantics Extensions

To generate semantic extensions, the SETS program can be used. By replacing `<sem>` with the appropriate abbreviation (`CF` for conflict-free, `AD` for admissible, or `ST` for stable) and `<inp>` with the input path of the AF, the program can produce the desired semantics.

```bash
python3 main.py SETS <inp> -s <sem>
```


### Determine Faithfulness/Spuriousness

Use the CHECK program to determine whether the abstract AF is faithful relative to the concrete AF. Replace `<abs>` with the file name of the abstract AF, `<con>` with the file name of the concrete AF and <sem> with the appropriate semantics. This tool enables verification of faithfulness between the abstract and concrete argumentation frameworks.

```bash
python3 main.py CHECK <abs> -c <con> -s <sem>
```

### Create Faithful AF

Use the FAITHFUL program to transform a spurious abstract AF <abs> into a faithful AF based on the concrete AF <con>. Additionally, replace <sem> with the corresponding semantics (i.e., `CF`, `AD`, or `ST`) to guide the transformation process. This ensures the resulting abstract AF aligns faithfully with the concrete AF under the specified semantics.

```bash
python3 main.py FAITHFUL <abs> -c <con> -s <sem>
```

### Concretize specific Arguments and Generate Faithful AF

Use the CONCRETIZE program to concretize a list of arguments and include additional arguments to ensure faithfulness. Replace `<abs>` with the abstract AF file, `<con>` with the concrete AF file, `<sem>` with the semantic abbreviation (i.e., `CF`, `AD`, or `ST`), and `<args>` with a space-separated list of arguments. This process helps maintain consistency and faithfulness between the abstract and concrete argumentation frameworks.

```bash
python3 main.py CONCRETIZE <abs> -c <con> -s <sem> -p <args>
```


## Optional Flags

| Flag | Description | Options |
| -------- | ----------- | ----------- |
| `f`  | Program to be executed | `SETS`, `CHECK`, `FAITHFUL`, `CONCRETIZE` | 
| `i`  | Path to the input file | - |
| `-c` | Defines the path of the file containing the concrete AF | - |
| `-s` | Defines the semantics | `CF`, `AD`, `ST` |
| `-a` | Specifies the algorithm | `BFS`, `DFS`|
| `-p` | Lists the arguments to be concretized separated by spaces | - |
| `-vis` | Boolean value to visualize AFs | `None` |
| `-verbose` | Boolean value to print additional computation steps | `None` |
| `-noref` | Boolean value to disable refinements| `None` |
| `-exp` | Boolean value to enter Experiment mode| `None`|



# References and Other Works
[Thesis: Computation of Clustered Argumentation Frameworks via Boolean Satisfiability](https://docs.google.com/viewer?url=https://fileserver.p4s3r0.it/personal/documents/MSc-thesis.pdf)

[Checking the acceptability of a set of arguments](https://www.researchgate.net/publication/221535800_Checking_the_acceptability_of_a_set_of_arguments)

[Existential Abstraction on Argumentation Frameworks via Clustering](https://proceedings.kr.org/2021/52/kr2021-0052-saribatur-et-al.pdf)

