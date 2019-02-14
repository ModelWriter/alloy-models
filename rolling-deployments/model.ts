import * as assert from 'assert';

/**
 * The states our simulated machines can be in.
 */
type MachineState = 'old' | 'new' | 'updating' | 'updated';

/**
 * This is really a state machine even though it doesn't look like one.
 * The transitions are of the following form:
 * 'old' -> 'updating' -> ... -> 'updated' -> 'new'. Each machine can
 * be in the 'updating' state for a configured amount of "time" to
 * simulated the fact that different machines can finish their
 * update process at different times because of various
 * vagaries of networked processes.
 */
class Machine {

  // 'old' is the start state for all machines.
  private state = 'old';

  /**
   * @param updateDelay Length of "time" the machine should be updating.
   */
  constructor(
    private updateDelay: number = 2 // Default length of "time" for updating
  ) { }

  /**
   * Perform the necessary violence to update the server. If the requisite
   * amount of "time" has passed then we also update the interal state to 'updated'.
   */
  doUpdateWork() {
    assert.equal(
      this.state, 'updating',
      `Update work is not allowed in this state: ${this.state}`
    );
    if (this.updateDelay-- <= 0) { this.state = 'updated'; }
  }

  /**
   * Start the update process for an old server. Just transitions from 'old' to 'updating'.
   */
  startUpdating() {
    assert.equal(
      this.state, 'old',
      `Starting the update process is not allowed in this state: ${this.state}`
    );
    this.state = 'updating';
  }

  /**
   * Put the server into production by updating the state from 'updated' to 'new'.
   */
  moveToProduction() {
    assert.equal(
      this.state, 'updated',
      `Not allowed to finish updating in this state: ${this.state}`
    );
    this.state = 'new';
  }

  // See if a machine is in a given state.

  get isUpdated() {
    return this.state === 'updated'; 
  }
  get isUpdating() {
    return this.state === 'updating';
  }
  get isOld() {
    return this.state === 'old';
  }
  get isNew() {
    return this.state === 'new';
  }
}

/**
 * Where we interact with the servers.
 */
class Environment {

  /**
   * @param machines List of machines in the environment. Passed in by whoever is running the simulation.
   */
  constructor(
    private machines: Machine[]
  ) { }

  // Various getters for the different classes of servers.

  get updatedServers() {
    return this.machines.filter(m => m.isUpdated);
  }
  get updatingServers() {
    return this.machines.filter(m => m.isUpdating);
  }
  get updatedMachines() {
    return this.machines.filter(m => m.isUpdated);
  }
  get allMachines() {
    return this.machines;
  }
  get newMachines() {
    return this.machines.filter(m => m.isNew);
  }

  /**
   * Pick some number of old servers to start the update process on them
   * @param count Number of old servers we want to concurrently start updating.
   */
  pickOldServers(count: number) {
    return this.machines.filter(m => m.isOld).slice(0, count);
  }

}

/**
 * The simulation driver
 */
class Simulation {

  constructor(
    private environment: Environment, // Someone else must give us the environment
    private concurrency: number = 2 // How many machines can we mess with at a time
  ) { }

  /**
   * One tick of the simulation.
   */
  doTick() {
    // Get any servers that have completed updating and move them into production
    console.log(`Moving servers that can move to production to production.`);
    const canMoveToProduction = this.environment.updatedMachines;
    canMoveToProduction.forEach(m => m.moveToProduction());
    console.log(`${canMoveToProduction.length} servers moved to production.`);

    // Find the list of updating servers and ask them to make forward progress
    const updatingServers = this.environment.updatingServers;
    console.log(`Found ${updatingServers.length} that still need to finish updating.`);
    updatingServers.forEach(m => m.doUpdateWork());

    // After asking the updating servers to do work see if we can start
    // updating some old servers
    const delta = this.concurrency - updatingServers.length;
    const oldServers = this.environment.pickOldServers(delta);
    console.log(`Concurrency delta is ${delta}.`);
    console.log(`Selecting ${oldServers.length} old servers for update process.`);
    if (updatingServers.length < this.concurrency) {
      oldServers.forEach(m => m.startUpdating());
    }

    // If all the servers are up to date then we are done
    const allMachines = this.environment.allMachines;
    const newMachines = this.environment.newMachines;
    console.log(`Total machines ${allMachines.length}.`);
    console.log(`New machines ${newMachines.length}.`);
    if (allMachines.length === newMachines.length) {
      console.log(`All servers are up to date.`);
      return true;
    }

    // Increment the tick counter for the next round although
    // it's not technically used for anything in the simulation
    // other than reporting
    console.log(`Rolling deployment still in progress.`);
    return false;
  }

  /**
   * Run the simulation to completion, i.e. perform the
   * update process to convert all old servers to new servers
   * in a rolling fashion.
   */
  run() {
    while (!this.doTick()) { }
  }
}

function main() {
  const machines: Machine[] = [];
  for (let i = 0; i < 10; i++) {
    machines.push(new Machine());
  }
  const environment = new Environment(machines);
  const simulation = new Simulation(environment)
  console.log(`Running simulation.`);
  simulation.run();
  console.log(`Simulation finished.`);
}

main();