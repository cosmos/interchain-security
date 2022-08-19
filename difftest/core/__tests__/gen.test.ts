import { gen } from '../src/main.js';

/**
 * This test is useful to check how much coverage
 * trace generation actually gets over the model.
 */
describe('generate traces', () => {
  it('dt', () => {
    gen(2);
    expect(true).toBeTruthy();
  });
});
