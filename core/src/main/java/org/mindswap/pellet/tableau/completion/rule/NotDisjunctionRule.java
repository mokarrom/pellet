package org.mindswap.pellet.tableau.completion.rule;

import java.util.List;

import org.mindswap.pellet.Individual;
import org.mindswap.pellet.Node;
import org.mindswap.pellet.tableau.branch.NotDisjunctionBranch;
import org.mindswap.pellet.tableau.completion.CompletionStrategy;
import org.mindswap.pellet.tableau.completion.queue.NodeSelector;
import org.mindswap.pellet.utils.ATermUtils;

import aterm.ATermAppl;
import aterm.ATermList;

public class NotDisjunctionRule extends AbstractTableauRule {
	public NotDisjunctionRule(CompletionStrategy strategy) {
		super( strategy, NodeSelector.NOTDISJUNCTION, BlockingType.COMPLETE );
	}

	public void apply(Individual node) {
		if( !node.canApply( Node.NOTOR ) )
			return;

		List<ATermAppl> types = node.getTypes( Node.NOTOR );

		int size = types.size();
		ATermAppl[] disjunctions = new ATermAppl[size - node.applyNext[Node.NOTOR]];
		types.subList( node.applyNext[Node.NOTOR], size ).toArray( disjunctions );
//		if( PelletOptions.USE_DISJUNCTION_SORTING != PelletOptions.NO_SORTING )
//			sortDisjunctions( node, disjunctions );

		for( int j = 0, n = disjunctions.length; j < n; j++ ) {
			ATermAppl disjunction = disjunctions[j];

			applyNotDisjunctionRule( node, disjunction );

			if( strategy.getABox().isClosed() || node.isMerged() )
				return;
		}
		node.applyNext[Node.NOTOR] = size;
	}
	
	/**
	 * Apply the not-disjunction rule to an specific label for an individual
	 * 
	 * @param node
	 * @param disjunction
	 */
	protected void applyNotDisjunctionRule(Individual node, ATermAppl disjunction) {
		// disjunction is now in the form qcnot( not( and([not(c1), not(c2), ...]) )  )
		ATermAppl a = (ATermAppl) disjunction.getArgument( 0 );
		ATermAppl b = (ATermAppl) a.getArgument( 0 );
		ATermList disjuncts = (ATermList) b.getArgument( 0 );
		ATermAppl[] disj = new ATermAppl[disjuncts.getLength()];
		ATermAppl[][] notDisj = new ATermAppl[3][2];
		
		for( int index = 0; !disjuncts.isEmpty(); disjuncts = disjuncts.getNext(), index++ ) {
			disj[index] = ATermUtils.negate( (ATermAppl) disjuncts.getFirst() );
//			if( node.hasType( disj[index] ) )
//				return;
		}
		
		notDisj[0][0] = ATermUtils.qcNegate(disj[0]);	notDisj[0][1] = ATermUtils.qcNegate(disj[1]);
		notDisj[1][0] = ATermUtils.negate(disj[0]);		notDisj[1][1] = ATermUtils.qcNegate(disj[1]);
		notDisj[2][0] = ATermUtils.qcNegate(disj[0]);	notDisj[2][1] = ATermUtils.negate(disj[1]);
		
		NotDisjunctionBranch newBranch = new NotDisjunctionBranch( strategy.getABox(), strategy, node,
				disjunction, node.getDepends( disjunction ), notDisj );
		strategy.addBranch( newBranch );

		newBranch.tryNext();
	}
	
}
