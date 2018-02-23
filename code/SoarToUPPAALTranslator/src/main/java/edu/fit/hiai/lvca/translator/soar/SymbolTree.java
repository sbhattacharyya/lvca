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
     * Return the first subtree (depth-first) that has the given name
     *
     * @param treeName
     * @return
     */
    SymbolTree getSubtree (String treeName)
    {
        SymbolTree result = getSubtree0(treeName);

        if (result == null)
        {
            throw new NoSuchElementException("Element not in tree");
        }
        return result;
    }

    private SymbolTree getSubtree0 (String treeName)
    {
        if (name.equals(treeName))
        {
            return this;
        }
        else
        {
            for (SymbolTree child : children)
            {
                if (child.getSubtree0(treeName) != null)
                {
                    return child;
                }
            }
        }
        return null;
    }

    /**
     * Give a underscore delimited string of parents to the first child of the given name
     * TODO return a list
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
     * Return a list of all paths from the root node to a leaf node, delimited by underscores
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

    List<SymbolTree> getChildren()
    {
        return children;
    }
}
