/** Local UI lifecycle: a late asynchronous render cannot replace a newer view. */
export interface PreparedPlot {
  mount(): void;
  dispose(): void;
}

export function createPlotSlot() {
  let revision = 0;
  let active: PreparedPlot | undefined;
  return {
    invalidate() {
      revision++;
      active?.dispose();
      active = undefined;
      return revision;
    },
    isCurrent(candidate: number) { return candidate === revision; },
    async show(candidate: number, render: () => Promise<PreparedPlot>) {
      if (candidate !== revision) return false;
      const plot = await render();
      if (candidate !== revision) {
        plot.dispose();
        return false;
      }
      try {
        plot.mount();
        active = plot;
        return true;
      } catch (error) {
        plot.dispose();
        throw error;
      }
    },
  };
}
