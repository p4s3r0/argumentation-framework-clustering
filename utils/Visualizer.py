# create the graph
import networkx as nx
import numpy as np
# plot the graph
import matplotlib.pyplot as plt
# setting seed to not randomize the graph drawing
import random
import numpy as np
from utils import Argument

def nudge(pos, x_shift, y_shift):
    return {n:(x + x_shift, y + y_shift) for n,(x,y) in pos.items()}


def show(data: dict):
    G = nx.DiGraph()
    edges = list()

    colors = list()
    clusters = list()
    singletons_in_cluster = list()
    singletons = list()


    for arg in data:
        for attack in data[arg].attacks:
            edges.append( (data[arg].name, attack) )
#
        if not data[arg].is_singleton:
            clusters.append(arg)
            for arg_cluster in data[arg].clustered_arguments:
                singletons_in_cluster.append(arg_cluster)

    for i in range(len(data)):
        node_name = str(i+1)
        if node_name not in clusters and node_name not in singletons_in_cluster:
            singletons.append(str(i+1))
        

    for arg in data:
        if arg in clusters:
            colors.append("#FF0000")
        else:
            colors.append("white")

    G.add_nodes_from([arg for arg in data])
    G.add_edges_from(edges)

    pos=nx.spring_layout(G)

    options = {
    "node_size": 2000,
    "edgecolors": "black",
    "arrowsize": 20,
    }


    nx.draw(G, pos, **options, node_color=colors)
    pos = nudge(pos, 0, -0.005)
    nx.draw_networkx_labels(G, pos, font_size=20)
    plt.show()


