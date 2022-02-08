# sassy
Tools for brute-force enumeration of set association schemes.

The user should have sage installed. See https://www.sagemath.org/. To run the find_all function it is also important to have a good integer programming backend such as gurobi. You can get a free academic license here: https://www.gurobi.com/.

Install with:

`sage -pip install git+https://github.com/seaneberhard/sassy`

The coherence of the 8 nonschurian set association schemes of degree 8 can be verified by running the jupyter notebook `verification.ipynb` with

`sage --jupyter notebook verification.ipynb`

(and inspecting the code in `sassy.py` for correctness).
