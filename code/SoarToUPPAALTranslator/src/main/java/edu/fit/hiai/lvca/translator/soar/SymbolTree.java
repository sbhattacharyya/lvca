package edu.fit.hiai.lvca.translator.soar;

import java.util.*;

/**
 * Created by mstafford on 6/17/16.
 *
 * Designed to capture the identifiers and hierarchy of a Soar agent
 */
public class SymbolTree
{
    final String name;
    private final List<SymbolTree> children;

    SymbolTree(String name)
    {
        this.name = name;
        children = new LinkedList<>();
    }

    private boolean isLeaf()
    {
        return children.size() == 0;
    }

    void addChild(SymbolTree childTree)
    {
        if (children.stream().noneMatch(c -> c.name.equals(childTree.name)))
        {
            children.add(childTree);
        }

    }

    /**
     * Conduct a depth-first search for the tree that has the given name, return that subtree.
     *
     * @param treeName
     * @return
     */
    SymbolTree getSubtree (String treeName)
    {
        SymbolTree result = getSubtreeNoError(treeName);

        if (result == null)
        {
            throw new NoSuchElementException("Element not in tree");
        }
        return result;
    }

    /**
     * @param treeName
     * Recursive companion to above method
     * @return
     */
    public SymbolTree getSubtreeNoError(String treeName)
    {
        if (name.equals(treeName))
        {
            return this;
        }
        else
        {
            for (SymbolTree child : children)
            {
                if (child.getSubtreeNoError(treeName) != null)
                {
                    return child;
                }
            }
        }
        return null;
    }

    public SymbolTree getSubtreeIgnoreUpdateAndCreate(String treeName) {
        if (name.equals(treeName))
        {
            return this;
        }
        else
        {
            for (SymbolTree child : children)
            {
                if (child.name.equals("update") || child.name.equals("create")) {
                    continue;
                } else if (child.getSubtreeNoError(treeName) != null)
                {
                    return child;
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
     * @param treeName
     * @return
     */
    String pathTo (String treeName)
    {
        if (name.equals(treeName))
        {
            return name;
        }

        String suffix = children.stream()
                .map(child -> child.pathTo(treeName))
                .filter(Objects::nonNull)
                .findFirst()
                .orElse(null);

        if (suffix != null)
        {
            return name + "_" + suffix;
        }
        else
        {
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
     * @return
     */
    List<String> getAllPaths()
    {
        if (isLeaf())
        {
            return Collections.singletonList(name);
        }
        else
        {
            List<String> names = new LinkedList<>();

            for (SymbolTree child : children)
            {
                for(String path : child.getAllPaths())
                {
                    names.add(name + "_" + path);
                }
            }

            return names;
        }
    }

    public int getIDFromTree() {
        SymbolTree createBranch = getSubtreeNoError("id");
        if (createBranch == null) {
            return -1;
        } else {
            return Integer.parseInt(createBranch.getChildren().get(0).getChildren().get(0).name);
        }
    }

    private void DFSForAttributeValuesUtiliy(LinkedList<SymbolTree> dfsCollection, SymbolTree currentTree) {
        for (SymbolTree child : currentTree.getChildren()) {
            if (child.getChildren().size() != 0 && !child.name.equals("create")) {
                DFSForAttributeValuesUtiliy(dfsCollection, child);
            }
        }
        if (currentTree.name.charAt(0) == '[') {
            dfsCollection.add(currentTree);
        }
    }

    public LinkedList<SymbolTree> DFSForAttributeValues() {
        LinkedList<SymbolTree> dfsCollection = new LinkedList<>();
        DFSForAttributeValuesUtiliy(dfsCollection, this);
        return dfsCollection;
    }

    List<SymbolTree> getChildren()
    {
        return children;
    }
}
