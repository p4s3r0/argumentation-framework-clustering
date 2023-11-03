# create the graph
import networkx as nx
import numpy as np
# plot the graph
import matplotlib.pyplot as plt
# setting seed to not randomize the graph drawing
import random
import numpy as np

def nudge(pos, x_shift, y_shift):
    return {n:(x + x_shift, y + y_shift) for n,(x,y) in pos.items()}


def show(data: dict):
    G = nx.DiGraph()
    edges = list()

    for arg in data:
        for attack in data[arg].attacks:
            edges.append( (data[arg].name, attack) )


    G.add_edges_from(edges)
    G.add_nodes_from([arg for arg in data])
    pos=nx.spring_layout(G)

    options = {
    "node_size": 2000,
    "node_color": "white",
    "edgecolors": "black",
    "arrowsize": 20,
    }

    nx.draw(G, pos, **options)
    pos = nudge(pos, 0, -0.005)
    nx.draw_networkx_labels(G, pos, font_size=20)
    plt.show()


