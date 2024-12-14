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

TODO

# References and Other Works
[Checking the acceptability of a set of arguments](https://www.researchgate.net/publication/221535800_Checking_the_acceptability_of_a_set_of_arguments)

[Existential Abstraction on Argumentation Frameworks via Clustering](https://proceedings.kr.org/2021/52/kr2021-0052-saribatur-et-al.pdf)

