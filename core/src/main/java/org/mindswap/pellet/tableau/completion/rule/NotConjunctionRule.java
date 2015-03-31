package org.mindswap.pellet.tableau.completion.rule;

import java.util.List;

import org.mindswap.pellet.Individual;
import org.mindswap.pellet.Node;
import org.mindswap.pellet.tableau.branch.DisjunctionBranch;
import org.mindswap.pellet.tableau.completion.CompletionStrategy;
import org.mindswap.pellet.tableau.completion.queue.NodeSelector;
import org.mindswap.pellet.utils.ATermUtils;

import aterm.ATermAppl;
import aterm.ATermList;

public class NotConjunctionRule extends AbstractTableauRule {
	public NotConjunctionRule(CompletionStrategy strategy) {
		super( strategy, NodeSelector.DISJUNCTION, BlockingType.COMPLETE );
	}
	
	public void apply(Individual node) {
		if( !node.canApply( Node.NOTAND ) )
			return;

		List<ATermAppl> types = node.getTypes( Node.NOTAND );

		int size = types.size();
		ATermAppl[] disjunctions = new ATermAppl[size - node.applyNext[Node.NOTAND]];
		types.subList( node.applyNext[Node.NOTAND], size ).toArray( disjunctions );
//		if( PelletOptions.USE_DISJUNCTION_SORTING != PelletOptions.NO_SORTING )
//			sortDisjunctions( node, disjunctions );

		for( int j = 0, n = disjunctions.length; j < n; j++ ) {
			ATermAppl disjunction = disjunctions[j];

			applyNotConjunctionRule( node, disjunction );

			if( strategy.getABox().isClosed() || node.isMerged() )
				return;
		}
		node.applyNext[Node.NOTAND] = size;
	}
	
	/**
	 * Apply the not-conjunction rule to an specific label for an individual
	 * 
	 * @param node
	 * @param disjunction
	 */
	protected void applyNotConjunctionRule(Individual node, ATermAppl notConjunction) {
		// notConjunction is now in the form qcnot( and( [c1, c2, ...] ) ) 	
		ATermAppl a = (ATermAppl) notConjunction.getArgument( 0 );
		ATermList disjuncts = (ATermList) a.getArgument( 0 );
		ATermAppl[] disj = new ATermAppl[disjuncts.getLength()];

		for( int index = 0; !disjuncts.isEmpty(); disjuncts = disjuncts.getNext(), index++ ) {
			disj[index] = ATermUtils.qcNegate( (ATermAppl) disjuncts.getFirst() );
		}
		
		if( node.hasType( disj[0] ) && node.hasType( disj[1] ) && disj.length < 3 )
			return;

		DisjunctionBranch newBranch = new DisjunctionBranch( strategy.getABox(), strategy, node,
				notConjunction, node.getDepends( notConjunction ), disj );
		strategy.addBranch( newBranch );

		newBranch.tryNext();
	}

}
