package edu.fit.hiai.lvca.translator.soar;

import java.util.*;

/**
 * Created by mstafford on 6/17/16.
 * Updated by Daniel Griessler during Summer 2018
 * Designed to capture the identifiers and hierarchy of a Soar agent
 */
public class SymbolTree
{
    final String name;
    private final List<SymbolTree> children;

    /**
     * Creates a new SymbolTree with the provided name
     * @param name Name of the new SymbolTree
     */
    SymbolTree(String name) {
        this.name = name;
        children = new LinkedList<>();
    }

    /**
     * Used to check if this a leaf like on a graph
     * @return If the SymbolTree has any children
     */
    public boolean isLeaf()
    {
        return children.size() == 0;
    }

    /**
     * Adds the provided SymbolTree to our list of children as long as we don't have a child with that name already
     * @param childTree Tree that will be added as the new child
     */
    void addChild(SymbolTree childTree) {
        if (children.stream().noneMatch(c -> c.name.equals(childTree.name))) {
            children.add(childTree);
        }

    }

    /**
     * Conduct a depth-first search for the tree that has the given name, return that subtree.
     * Throws a NoSuchElementException if it can't be found
     *
     * @param treeName Name of the tree to be found
     * @return SymbolTree with that name.  Will throw exception if not found
     */
    SymbolTree getSubtree (String treeName) {
        SymbolTree result = getSubtreeNoError(treeName);

        if (result == null) {
            throw new NoSuchElementException("Element not in tree");
        }
        return result;
    }

    /**
     * Duplicate of getSubtree but will return null if it can't find the tree instead of throwing an error
     * @param treeName Name of the tree to be found
     * @return SymbolTree with that name or null if it can't be found
     */
    public SymbolTree getSubtreeNoError(String treeName) {
        if (name.equals(treeName)) {
            return this;
        } else {
            for (SymbolTree child : children) {
                if (child.getSubtreeNoError(treeName) != null) {
                    return child;
                }
            }
        }
        return null;
    }

    /**
     * Depth First Search of the children to find the provided tree name
     * @param treeName Name of the tree to be found
     * @return SymbolTree with that name or null if it can't be found
     */
    public SymbolTree DFS(String treeName) {
        if (name.equals(treeName)) {
            return this;
        } else {
            for (SymbolTree child : children) {
                SymbolTree childTree = child.getSubtreeNoError(treeName);
                if (childTree != null) {
                    return childTree;
                }
            }
        }
        return null;
    }

    /**
     * Give a underscore delimited string of parents to the first child of the given name, like a file path.
     *
     * E.g. grandparent_parent_child
     *
     * @param treeName Name of the tree to be found
     * @return Underscore delimited string of parents to the first child of the given name or null if the tree can't be found
     */
    String pathTo (String treeName) {
        if (name.equals(treeName)) {
            return name;
        }

        String suffix = children.stream()
                .map(child -> child.pathTo(treeName))
                .filter(Objects::nonNull)
                .findFirst()
                .orElse(null);

        if (suffix != null) {
            return name + "_" + suffix;
        } else {
            return null;
        }
    }

    /**
     * Return a list of all paths from the root node terminating in a leaf node, delimited by underscores.
     *
     * E.g.
     *  grandparent_parent_firstChild
     *  grandparent_parent_secondChild
     *  grandparent_childlessUncle
     *
     *
     * @return A list of all paths from the root node terminating in a leaf node, delimited by underscores.
     */
    List<String> getAllPaths()
    {
        if (isLeaf()) {
            return Collections.singletonList(name);
        } else {
            List<String> names = new LinkedList<>();

            for (SymbolTree child : children) {
                for(String path : child.getAllPaths()) {
                    names.add(name + "_" + path);
                }
            }

            return names;
        }
    }

    List<SymbolTree> getChildren() { return children; }
}
