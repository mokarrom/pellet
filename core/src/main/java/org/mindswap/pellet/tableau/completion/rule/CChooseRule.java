package org.mindswap.pellet.tableau.completion.rule;

import java.util.Iterator;
import java.util.List;

import org.mindswap.pellet.Edge;
import org.mindswap.pellet.EdgeList;
import org.mindswap.pellet.Individual;
import org.mindswap.pellet.Node;
import org.mindswap.pellet.PelletOptions;
import org.mindswap.pellet.Role;
import org.mindswap.pellet.tableau.branch.ChooseBranch;
import org.mindswap.pellet.tableau.completion.CompletionStrategy;
import org.mindswap.pellet.tableau.completion.queue.NodeSelector;
import org.mindswap.pellet.tableau.completion.rule.AbstractTableauRule.BlockingType;
import org.mindswap.pellet.utils.ATermUtils;

import aterm.ATermAppl;

public class CChooseRule extends AbstractTableauRule {
	
	public CChooseRule(CompletionStrategy strategy) {
		super( strategy, NodeSelector.CCHOOSE, BlockingType.INDIRECT );
	}
	
	public void apply( Individual x ) {
        if( !x.canApply( Individual.NOTMIN ) )
        	return;

        List<ATermAppl> maxCardinality = x.getTypes( Node.NOTMIN );
        Iterator<ATermAppl> j = maxCardinality.iterator();

        while( j.hasNext() ) {
        	ATermAppl maxCard = j.next();
        	apply( x, maxCard );
        }
    }
	
	protected void apply( Individual x, ATermAppl maxCard ) { 
		// notmin(r, n, c) is in normalized form qcnot(min(r, n, c))
        ATermAppl max = (ATermAppl) maxCard.getArgument( 0 );	//now, max = min(r, n, c)
        Role r = strategy.getABox().getRole( max.getArgument( 0 ) );
        ATermAppl c = (ATermAppl) max.getArgument( 2 );
        c = ATermUtils.negate( c );
        
        if( ATermUtils.isTop( c ) )
            return;
        
        if(!PelletOptions.MAINTAIN_COMPLETION_QUEUE && x.getDepends(maxCard) == null)
    			return;

        EdgeList edges = x.getRNeighborEdges( r );
        for( Iterator<Edge> i = edges.iterator(); i.hasNext(); ) {
            Edge edge = i.next();
            Node neighbor = edge.getNeighbor( x );

            if( !neighbor.hasType( c ) && !neighbor.hasType( ATermUtils.qcNegate( c ) ) ) {
                ChooseBranch newBranch = new ChooseBranch( strategy.getABox(), strategy, neighbor, c, x
                    .getDepends( maxCard ) );
                strategy.addBranch( newBranch );

                newBranch.tryNext();

                if( strategy.getABox().isClosed() )
                    return;
            }
        }    	
    }
}
