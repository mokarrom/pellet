package org.mindswap.pellet.tableau.completion;

import static com.clarkparsia.pellet.utils.TermFactory.TOP_OBJECT_PROPERTY;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.logging.Level;

import org.mindswap.pellet.ABox;
import org.mindswap.pellet.DependencySet;
import org.mindswap.pellet.Edge;
import org.mindswap.pellet.EdgeList;
import org.mindswap.pellet.Individual;
import org.mindswap.pellet.IndividualIterator;
import org.mindswap.pellet.Node;
import org.mindswap.pellet.NodeMerge;
import org.mindswap.pellet.PelletOptions;
import org.mindswap.pellet.Role;
import org.mindswap.pellet.exceptions.InternalReasonerException;
import org.mindswap.pellet.tableau.blocking.BlockingFactory;
import org.mindswap.pellet.tableau.branch.Branch;
import org.mindswap.pellet.tableau.completion.rule.TableauRule;
import org.mindswap.pellet.tbox.impl.Unfolding;
import org.mindswap.pellet.utils.ATermUtils;

import aterm.ATermAppl;

import com.clarkparsia.pellet.expressivity.Expressivity;

public class QCALCStrategy extends CompletionStrategy {

	public QCALCStrategy(ABox abox) {
		super( abox );
	}
	
	protected boolean backtrack() {
		boolean branchFound = false;
		abox.stats.backtracks++;
		while( !branchFound ) {
			completionTimer.check();

			int lastBranch = abox.getClash().getDepends().max();

			// not more branches to try
			if( lastBranch <= 0 )
				return false;
			else if( lastBranch > abox.getBranches().size() )
				throw new InternalReasonerException( "Backtrack: Trying to backtrack to branch "
						+ lastBranch + " but has only " + abox.getBranches().size()
						+ " branches. Clash found: " + abox.getClash() );
			else if( PelletOptions.USE_INCREMENTAL_DELETION ) {
				// get the last branch
				Branch br = abox.getBranches().get( lastBranch - 1 );

				// if this is the last disjunction, merge pair, etc. for the
				// branch (i.e, br.tryNext == br.tryCount-1) and there are no
				// other branches to test (ie.
				// abox.getClash().depends.size()==2),
				// then update depedency index and return false
				if( (br.getTryNext() == br.getTryCount() - 1)
						&& abox.getClash().getDepends().size() == 2 ) {
					abox.getKB().getDependencyIndex().addCloseBranchDependency( br,
							abox.getClash().getDepends() );
					return false;
				}
			}

			List<Branch> branches = abox.getBranches();
			abox.stats.backjumps += (branches.size() - lastBranch);
			// CHW - added for incremental deletion support
			if( PelletOptions.USE_TRACING && PelletOptions.USE_INCREMENTAL_CONSISTENCY ) {
				// we must clean up the KB dependecny index
				List<Branch> brList = branches.subList( lastBranch, branches.size() );
				for( Iterator<Branch> it = brList.iterator(); it.hasNext(); ) {
					// remove from the dependency index
					abox.getKB().getDependencyIndex().removeBranchDependencies( it.next() );
				}
				brList.clear();
			}
			else {
				// old approach
				branches.subList( lastBranch, branches.size() ).clear();
			}

			// get the branch to try
			Branch newBranch = branches.get( lastBranch - 1 );

			if( log.isLoggable( Level.FINE ) )
				log.fine( "JUMP: Branch " + lastBranch );

			if( lastBranch != newBranch.getBranch() )
				throw new InternalReasonerException( "Backtrack: Trying to backtrack to branch "
						+ lastBranch + " but got " + newBranch.getBranch() );

			// set the last clash before restore
			if( newBranch.getTryNext() < newBranch.getTryCount() ) {
				newBranch.setLastClash( abox.getClash().getDepends() );
			}

			// increment the counter
			newBranch.setTryNext( newBranch.getTryNext() + 1 );

			// no need to restore this branch if we exhausted possibilities
			if( newBranch.getTryNext() < newBranch.getTryCount() ) {
				// undo the changes done after this branch
				restore( newBranch );
			}

			// try the next possibility
			branchFound = newBranch.tryNext();

			if( !branchFound ) {
				if( log.isLoggable( Level.FINE ) )
					log.fine( "FAIL: Branch " + lastBranch );
			}
		}

		return branchFound;
	}
	
	public void initialize(Expressivity expressivity) {
		mergeList = new ArrayList<NodeMerge>();

		blocking = BlockingFactory.createBlocking(expressivity);

		configureTableauRules(expressivity);

		for (Branch branch : abox.getBranches()) {
			branch.setStrategy(this);
		}
		
		if (abox.isInitialized()) {

			Iterator<Individual> i = getInitializeIterator();
			while (i.hasNext()) {
				Individual n = i.next();

				if (n.isMerged()) {
					continue;
				}

				if (n.isConceptRoot()) {
					applyUniversalRestrictions(n);
				}

				allValuesRule.apply(n);
				if (n.isMerged()) {
					continue;
				}
				nominalRule.apply(n);
				if (n.isMerged()) {
					continue;
				}
				selfRule.apply(n);

				// CHW-added for inc. queue must see if this is bad
				EdgeList allEdges = n.getOutEdges();
				for (int e = 0; e < allEdges.size(); e++) {
					Edge edge = allEdges.edgeAt(e);
					if (edge.getTo().isPruned()) {
						continue;
					}

					applyPropertyRestrictions(edge);
					if (n.isMerged()) {
						break;
					}
				}

			}

			return;
		}

		if (log.isLoggable(Level.FINE)) {
			log.fine("Initialize started");
		}

		abox.setBranch(0);
		
		mergeList.addAll(abox.getToBeMerged());
		
		if (!mergeList.isEmpty()) {
			mergeAll();
		}

		Role topRole = abox.getRole(TOP_OBJECT_PROPERTY);
		Iterator<Individual> i = getInitializeIterator();
		while (i.hasNext()) {
			Individual n = i.next();

			//Add internalize concepts to the node 
			List<Unfolding> intConceptList = tbox.getTC();
	        int size = intConceptList.size();
	        for( int j = 0; j < size; j++ ) {
	        	 Unfolding intConcept = intConceptList.get(j);
	        	 ATermAppl c = intConcept.getResult();
	        	 
	        	 DependencySet ds = DependencySet.INDEPENDENT;
	        	 
	        	 if (log.isLoggable(Level.FINE)) {
	     			log.fine("Node: " + n + " # adding internalize concept: " + ATermUtils.toString(c));
	     		 }
	        	 
	        	 addType( n, c , ds );
	        }
			
			if (n.isMerged()) {
				continue;
			}

			applyUniversalRestrictions(n);
			if (n.isMerged()) {
				continue;
			}

			selfRule.apply(n);
			if (n.isMerged()) {
				continue;
			}

			EdgeList allEdges = n.getOutEdges();
			for (int e = 0; e < allEdges.size(); e++) {
				Edge edge = allEdges.edgeAt(e);

				if (edge.getTo().isPruned()) {
					continue;
				}

				applyPropertyRestrictions(edge);

				if (n.isMerged()) {
					break;
				}
			}

			if (n.isMerged()) {
				continue;
			}

			// The top object role isn't in the edge list, so pretend it exists
			applyPropertyRestrictions(n, topRole, n, DependencySet.INDEPENDENT);
		}

		if (log.isLoggable(Level.FINE)) {
			log.fine("Merging: " + mergeList);
		}

		if (!mergeList.isEmpty()) {
			mergeAll();
		}

		if (log.isLoggable(Level.FINE)) {
			log.fine("Initialize finished");
		}

		abox.setBranch(abox.getBranches().size() + 1);
		abox.stats.treeDepth = 1;
		abox.setChanged(true);
		abox.setComplete(false);
		abox.setInitialized(true);
	}
	
	public void complete(Expressivity expr) {
		initialize( expr );
		
		while( !abox.isComplete() ) {
			while( abox.isChanged() && !abox.isClosed() ) {
				completionTimer.check();

				abox.setChanged( false );

				if( log.isLoggable( Level.FINE ) ) {
					log.fine( "Branch: " + abox.getBranch() + ", Depth: " + abox.stats.treeDepth
							+ ", Size: " + abox.getNodes().size() + ", Mem: "
							+ (Runtime.getRuntime().freeMemory() / 1000) + "kb" );
					abox.validate();
					printBlocked();
					abox.printTree();
				}

				IndividualIterator i = (PelletOptions.USE_COMPLETION_QUEUE)
					? abox.getCompletionQueue()
					: abox.getIndIterator();

				// flush the queue
				if( PelletOptions.USE_COMPLETION_QUEUE )
					abox.getCompletionQueue().flushQueue();

				for( TableauRule tableauRule : tableauRules ) {
					tableauRule.apply( i );
					if( abox.isClosed() )
						break;
				}

				// it could be the case that there was a clash and we had a
				// deletion update that retracted it
				// however there could have been some thing on the queue that
				// still needed to be refired from backtracking
				// so onle set that the abox is clash free after we have applied
				// all the rules once
				if( PelletOptions.USE_COMPLETION_QUEUE )
					abox.getCompletionQueue().setClosed( abox.isClosed() );
			}

			if( abox.isClosed() ) {
				if( log.isLoggable( Level.FINE ) )
					log.fine( "Clash at Branch (" + abox.getBranch() + ") " + abox.getClash() );

				if( backtrack() ) {
					abox.setClash( null );

					if( PelletOptions.USE_COMPLETION_QUEUE )
						abox.getCompletionQueue().setClosed( false );
				}
				else {
					abox.setComplete( true );

					// we need to flush the queue to add the other elements
					if( PelletOptions.USE_COMPLETION_QUEUE )
						abox.getCompletionQueue().flushQueue();
				}
			}
			else {
				if( PelletOptions.SATURATE_TABLEAU ) {
					Branch unexploredBranch = null;
					for( int i = abox.getBranches().size() - 1; i >= 0; i-- ) {
						unexploredBranch = abox.getBranches().get( i );
						unexploredBranch.setTryNext( unexploredBranch.getTryNext() + 1 );
						if( unexploredBranch.getTryNext() < unexploredBranch.getTryCount() ) {
							restore( unexploredBranch );
							System.out.println( "restoring branch " + unexploredBranch.getBranch()
									+ " tryNext = " + unexploredBranch.getTryNext()
									+ " tryCount = " + unexploredBranch.getTryCount() );
							unexploredBranch.tryNext();
							break;
						}
						else {
							System.out.println( "removing branch " + unexploredBranch.getBranch() );
							abox.getBranches().remove( i );
							unexploredBranch = null;
						}
					}
					if( unexploredBranch == null ) {
						abox.setComplete( true );
					}
				}
				else
					abox.setComplete( true );
			}
		}
	}//end complete 
	
}//end QCALCStrategy

