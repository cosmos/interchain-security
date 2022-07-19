import { gen } from '../src/main.js';

describe('tests are working', () => {
  it('dt', () => {
    gen(2);
    expect(true).toBeTruthy();
  });
});
