# argumentation-framework-clustering
GitHub Repository for my Master's Thesis in Computer Science at the University of Technology Graz

## Important Formulas

### Conflict Free Sets
$$ \bigwedge_{a \in A_{SINGLETONS}} \big( \bigwedge_{b:(b,a)\in R, b \in A_{SINGLETONS}} \lnot \big( a \wedge b \big) \big)$$

### Admissible Sets
$$ \bigwedge_{a \in A_{SINGLETONS}} \big( \bigwedge_{b:(b,a)\in R, b \in A_{SINGLETONS}} \lnot \big( a \wedge b \big) \land \big( a \rightarrow \bigwedge_{b:(b,a) \in R} \big( \bigvee_{c:(c,b) \in R} c\big) \big)\big)$$


### Stable Sets 
$$ \bigwedge_{a \in A_{SINGLETONS}} \big( \bigwedge_{b:(b,a)\in R, b \in A_{SINGLETONS}} \lnot \big( a \wedge b \big) \big) \land \bigwedge_{a \in A} \big( a \bigvee_{b:(b,a)\in R} b\big) \land \bigwedge_{a \in A} \big( \big(  a \bigwedge_{b:(b,a) \in R} \lnot b\big) \big) \rightarrow \big( \bigwedge_{c:(a,c), c \in A_{SINGLETONS}} \lnot c\big)$$

# References and Other Works
[Checking the acceptability of a set of arguments](https://www.pims.math.ca/science/2004/NMR/papers/paper08.pdf)

[Existential Abstraction on Argumentation Frameworks via Clustering](https://proceedings.kr.org/2021/52/kr2021-0052-saribatur-et-al.pdf)

